module

public import ErdosSzekeres.Fin15AnchoredClauseChunk209
public import ErdosSzekeres.Fin15AnchoredClauseChunk210

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 106. -/

theorem fin15Anchored_rejectSemanticSegment106
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom4442 chi ∧
      ¬Fin15AnchoredAtom1691 chi) ∨
      ((¬Fin15AnchoredAtom4442 chi ∧
      Fin15AnchoredAtom1521 chi ∧
      Fin15AnchoredAtom1522 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1607 chi ∧
      Fin15AnchoredAtom1691 chi) ∨
      (Fin15AnchoredAtom4443 chi ∧
      ¬Fin15AnchoredAtom1692 chi))) ∨
      (((Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom1524 chi) ∨
      (Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom1525 chi)) ∨
      ((Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom1526 chi) ∨
      (Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom1610 chi)))) ∨
      ((((Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom1694 chi) ∨
      (¬Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1694 chi)) ∨
      ((Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom1527 chi) ∨
      (Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom1528 chi))) ∨
      (((Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom1534 chi) ∨
      (Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom1555 chi)) ∨
      ((Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom1695 chi) ∨
      (¬Fin15AnchoredAtom4446 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1695 chi))))) ∨
      (((((Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom1527 chi) ∨
      (Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom1529 chi)) ∨
      ((Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom1535 chi) ∨
      (Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom1556 chi))) ∨
      (((Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom1696 chi) ∨
      (¬Fin15AnchoredAtom4447 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1696 chi)) ∨
      ((Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom1527 chi) ∨
      (Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom1531 chi)))) ∨
      ((((Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom1537 chi) ∨
      (Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom1558 chi)) ∨
      ((Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (¬Fin15AnchoredAtom4449 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1698 chi))) ∨
      (((Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom1527 chi) ∨
      (Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom1532 chi)) ∨
      ((Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom1559 chi) ∨
      (Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom1699 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom4450 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1699 chi) ∨
      (Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom1527 chi)) ∨
      ((Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom1533 chi) ∨
      (Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom1539 chi))) ∨
      (((Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom1560 chi) ∨
      (Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom1700 chi)) ∨
      ((¬Fin15AnchoredAtom4451 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1700 chi) ∨
      (Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom1528 chi)))) ∨
      ((((Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom1529 chi) ∨
      (Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom1540 chi)) ∨
      ((Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom1561 chi) ∨
      (Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom1701 chi))) ∨
      (((¬Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1701 chi) ∨
      (Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom1528 chi)) ∨
      ((Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom1530 chi) ∨
      (Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom1541 chi))))) ∨
      (((((Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom1562 chi) ∨
      (¬Fin15AnchoredAtom4453 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1530 chi ∧
      Fin15AnchoredAtom1541 chi ∧
      Fin15AnchoredAtom1562 chi ∧
      Fin15AnchoredAtom1702 chi)) ∨
      ((Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom1528 chi) ∨
      (Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom1531 chi))) ∨
      (((Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom1563 chi)) ∨
      ((Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom1703 chi) ∨
      (¬Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1703 chi)))) ∨
      ((((Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom1528 chi) ∨
      (Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom1532 chi)) ∨
      ((Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom1543 chi) ∨
      (Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom1564 chi))) ∨
      (((Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom1704 chi) ∨
      (¬Fin15AnchoredAtom4455 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1704 chi)) ∨
      ((Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom1528 chi) ∨
      (Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom1533 chi))))))) ∨
      ((((((Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom1544 chi) ∨
      ((Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom1565 chi) ∨
      (Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom1705 chi))) ∨
      (((¬Fin15AnchoredAtom4456 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1705 chi) ∨
      (Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom1529 chi)) ∨
      ((Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom1530 chi) ∨
      (Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom1566 chi)))) ∨
      ((((Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom1529 chi) ∨
      (Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom1531 chi)) ∨
      ((Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom1546 chi) ∨
      (Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom1567 chi))) ∨
      (((Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom1707 chi) ∨
      (¬Fin15AnchoredAtom4458 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1707 chi)) ∨
      ((Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom1529 chi) ∨
      (Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom1532 chi))))) ∨
      (((((Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom1547 chi) ∨
      (Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom1568 chi)) ∨
      ((Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom1708 chi) ∨
      (¬Fin15AnchoredAtom4459 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1708 chi))) ∨
      (((Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom1529 chi) ∨
      (Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom1533 chi)) ∨
      ((Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom1548 chi) ∨
      (Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom1569 chi)))) ∨
      ((((Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom1709 chi) ∨
      (¬Fin15AnchoredAtom4460 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1709 chi)) ∨
      ((Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom1530 chi) ∨
      (Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom1531 chi))) ∨
      (((Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom1549 chi) ∨
      (Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom1710 chi)) ∨
      ((¬Fin15AnchoredAtom4461 chi ∧
      Fin15AnchoredAtom1530 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1549 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1710 chi) ∨
      (Fin15AnchoredAtom4462 chi ∧
      ¬Fin15AnchoredAtom1530 chi)))))) ∨
      ((((((Fin15AnchoredAtom4462 chi ∧
      ¬Fin15AnchoredAtom1532 chi) ∨
      (Fin15AnchoredAtom4463 chi ∧
      ¬Fin15AnchoredAtom1533 chi)) ∨
      ((Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom1531 chi) ∨
      (Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom1532 chi))) ∨
      (((Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom1552 chi) ∨
      (Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom1573 chi)) ∨
      ((Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom1713 chi) ∨
      (¬Fin15AnchoredAtom4464 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1713 chi)))) ∨
      ((((Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom1531 chi) ∨
      (Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom1533 chi)) ∨
      ((Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom1553 chi) ∨
      (Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom1574 chi))) ∨
      (((Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom1714 chi) ∨
      (¬Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1714 chi)) ∨
      ((Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom1532 chi) ∨
      (Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom1533 chi))))) ∨
      (((((Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom1554 chi) ∨
      (Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom1575 chi)) ∨
      ((Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom1715 chi) ∨
      (¬Fin15AnchoredAtom4466 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1715 chi))) ∨
      (((Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom1534 chi) ∨
      (Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom1535 chi)) ∨
      ((Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom1540 chi) ∨
      (Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom1576 chi)))) ∨
      ((((Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom1716 chi) ∨
      (¬Fin15AnchoredAtom4467 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1576 chi ∧
      Fin15AnchoredAtom1716 chi)) ∨
      ((Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom1534 chi) ∨
      (Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom1537 chi))) ∨
      (((Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom1578 chi)) ∨
      ((Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom1718 chi) ∨
      (¬Fin15AnchoredAtom4469 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1718 chi)))))))) ∨
      (((((((Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom1534 chi) ∨
      ((Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom1538 chi) ∨
      (Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom1543 chi))) ∨
      (((Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom1579 chi) ∨
      (Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom1719 chi)) ∨
      ((¬Fin15AnchoredAtom4470 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1719 chi) ∨
      (Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom1534 chi)))) ∨
      ((((Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom1539 chi) ∨
      (Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom1544 chi)) ∨
      ((Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom1580 chi) ∨
      (Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom1720 chi))) ∨
      (((¬Fin15AnchoredAtom4471 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1580 chi ∧
      Fin15AnchoredAtom1720 chi) ∨
      (Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom1535 chi)) ∨
      ((Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom1537 chi) ∨
      (Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom1546 chi))))) ∨
      (((((Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom1582 chi) ∨
      (Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom1722 chi)) ∨
      ((¬Fin15AnchoredAtom4473 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1722 chi) ∨
      (Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom1535 chi))) ∨
      (((Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom1538 chi) ∨
      (Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom1547 chi)) ∨
      ((Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom1583 chi) ∨
      (Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom1723 chi)))) ∨
      ((((¬Fin15AnchoredAtom4474 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1723 chi) ∨
      (Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom1535 chi)) ∨
      ((Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom1539 chi) ∨
      (Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom1548 chi))) ∨
      (((Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom1584 chi) ∨
      (Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom1724 chi)) ∨
      ((¬Fin15AnchoredAtom4475 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1584 chi ∧
      Fin15AnchoredAtom1724 chi) ∨
      (Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom1537 chi)))))) ∨
      ((((((Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom1538 chi) ∨
      (Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom1552 chi)) ∨
      ((Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom1588 chi) ∨
      (Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom1728 chi))) ∨
      (((¬Fin15AnchoredAtom4479 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1728 chi) ∨
      (Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom1537 chi)) ∨
      ((Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom1539 chi) ∨
      (Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom1553 chi)))) ∨
      ((((Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom1589 chi) ∨
      (Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom1729 chi)) ∨
      ((¬Fin15AnchoredAtom4480 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1729 chi) ∨
      (Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom1538 chi))) ∨
      (((Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom1539 chi) ∨
      (Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom1554 chi)) ∨
      ((Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom1590 chi) ∨
      (Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom1730 chi))))) ∨
      (((((¬Fin15AnchoredAtom4481 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1730 chi) ∨
      (Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom1540 chi)) ∨
      ((Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom1541 chi) ∨
      (Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom1545 chi))) ∨
      (((Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom1591 chi) ∨
      (Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom1731 chi)) ∨
      ((¬Fin15AnchoredAtom4482 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1541 chi ∧
      Fin15AnchoredAtom1545 chi ∧
      Fin15AnchoredAtom1591 chi ∧
      Fin15AnchoredAtom1731 chi) ∨
      (Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom1540 chi)))) ∨
      ((((Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom1546 chi)) ∨
      ((Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom1592 chi) ∨
      (Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom1732 chi))) ∨
      (((¬Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1732 chi) ∨
      (Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom1540 chi)) ∨
      ((Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom1543 chi) ∨
      (Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom1547 chi))))))) ∨
      ((((((Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom1593 chi) ∨
      ((Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom1733 chi) ∨
      (¬Fin15AnchoredAtom4484 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1733 chi))) ∨
      (((Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom1540 chi) ∨
      (Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom1544 chi)) ∨
      ((Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom1548 chi) ∨
      (Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom1594 chi)))) ∨
      ((((Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom1734 chi) ∨
      (¬Fin15AnchoredAtom4485 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1594 chi ∧
      Fin15AnchoredAtom1734 chi)) ∨
      ((Fin15AnchoredAtom4486 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (Fin15AnchoredAtom4486 chi ∧
      ¬Fin15AnchoredAtom1549 chi))) ∨
      (((Fin15AnchoredAtom4486 chi ∧
      ¬Fin15AnchoredAtom1735 chi) ∨
      (¬Fin15AnchoredAtom4486 chi ∧
      Fin15AnchoredAtom1541 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1549 chi ∧
      Fin15AnchoredAtom1595 chi ∧
      Fin15AnchoredAtom1735 chi)) ∨
      ((Fin15AnchoredAtom4487 chi ∧
      ¬Fin15AnchoredAtom1543 chi) ∨
      (Fin15AnchoredAtom4487 chi ∧
      ¬Fin15AnchoredAtom1596 chi))))) ∨
      (((((Fin15AnchoredAtom4487 chi ∧
      ¬Fin15AnchoredAtom1736 chi) ∨
      (Fin15AnchoredAtom4488 chi ∧
      ¬Fin15AnchoredAtom1544 chi)) ∨
      ((Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom1543 chi))) ∨
      (((Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom1552 chi) ∨
      (Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom1598 chi)) ∨
      ((Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom1738 chi) ∨
      (¬Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1738 chi)))) ∨
      ((((Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom1544 chi)) ∨
      ((Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom1553 chi) ∨
      (Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom1599 chi))) ∨
      (((Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom1739 chi) ∨
      (¬Fin15AnchoredAtom4490 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1739 chi)) ∨
      ((Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom1543 chi) ∨
      (Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom1544 chi)))))) ∨
      ((((((Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom1554 chi) ∨
      (Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom1600 chi)) ∨
      ((Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom1740 chi) ∨
      (¬Fin15AnchoredAtom4491 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1740 chi))) ∨
      (((Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom1546 chi) ∨
      (Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom1549 chi)) ∨
      ((Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom1741 chi) ∨
      (Fin15AnchoredAtom4493 chi ∧
      ¬Fin15AnchoredAtom1547 chi)))) ∨
      ((((Fin15AnchoredAtom4493 chi ∧
      ¬Fin15AnchoredAtom1602 chi) ∨
      (¬Fin15AnchoredAtom4493 chi ∧
      Fin15AnchoredAtom1545 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1550 chi ∧
      Fin15AnchoredAtom1602 chi ∧
      Fin15AnchoredAtom1742 chi)) ∨
      ((Fin15AnchoredAtom4494 chi ∧
      ¬Fin15AnchoredAtom1548 chi) ∨
      (Fin15AnchoredAtom4494 chi ∧
      ¬Fin15AnchoredAtom1551 chi))) ∨
      (((Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom1546 chi) ∨
      (Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom1547 chi)) ∨
      ((Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom1552 chi) ∨
      (Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom1604 chi))))) ∨
      (((((Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom1744 chi) ∨
      (¬Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1744 chi)) ∨
      ((Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom1546 chi) ∨
      (Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom1548 chi))) ∨
      (((Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom1553 chi) ∨
      (Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom1605 chi)) ∨
      ((Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom1745 chi) ∨
      (¬Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1745 chi)))) ∨
      ((((Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom1547 chi) ∨
      (Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom1548 chi)) ∨
      ((Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom1554 chi) ∨
      (Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom1606 chi))) ∨
      (((Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom1746 chi) ∨
      (¬Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1746 chi)) ∨
      ((Fin15AnchoredAtom4498 chi ∧
      ¬Fin15AnchoredAtom1552 chi) ∨
      (Fin15AnchoredAtom4498 chi ∧
      ¬Fin15AnchoredAtom1607 chi)))))))))) := by
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
                exact fin15Anchored_clause26755 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26756 chi hbad
                ·
                  exact fin15Anchored_clause26757 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26758 chi hbad
                ·
                  exact fin15Anchored_clause26759 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26760 chi hbad
                ·
                  exact fin15Anchored_clause26761 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26762 chi hbad
                ·
                  exact fin15Anchored_clause26763 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26764 chi hbad
                ·
                  exact fin15Anchored_clause26765 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26766 chi hbad
                ·
                  exact fin15Anchored_clause26767 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26768 chi hbad
                ·
                  exact fin15Anchored_clause26769 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26770 chi hbad
                ·
                  exact fin15Anchored_clause26771 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26772 chi hbad
                ·
                  exact fin15Anchored_clause26773 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26774 chi hbad
                ·
                  exact fin15Anchored_clause26775 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26776 chi hbad
                ·
                  exact fin15Anchored_clause26777 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26778 chi hbad
                ·
                  exact fin15Anchored_clause26779 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26780 chi hbad
                ·
                  exact fin15Anchored_clause26781 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26782 chi hbad
                ·
                  exact fin15Anchored_clause26783 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26784 chi hbad
                ·
                  exact fin15Anchored_clause26785 chi hbad
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
                  exact fin15Anchored_clause26786 chi hbad
                ·
                  exact fin15Anchored_clause26787 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26788 chi hbad
                ·
                  exact fin15Anchored_clause26789 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26790 chi hbad
                ·
                  exact fin15Anchored_clause26791 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26792 chi hbad
                ·
                  exact fin15Anchored_clause26793 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26794 chi hbad
                ·
                  exact fin15Anchored_clause26795 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26796 chi hbad
                ·
                  exact fin15Anchored_clause26797 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26798 chi hbad
                ·
                  exact fin15Anchored_clause26799 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26800 chi hbad
                ·
                  exact fin15Anchored_clause26801 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26802 chi hbad
                ·
                  exact fin15Anchored_clause26803 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26804 chi hbad
                ·
                  exact fin15Anchored_clause26805 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26806 chi hbad
                ·
                  exact fin15Anchored_clause26807 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26808 chi hbad
                ·
                  exact fin15Anchored_clause26809 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26810 chi hbad
                ·
                  exact fin15Anchored_clause26811 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26812 chi hbad
                ·
                  exact fin15Anchored_clause26813 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26814 chi hbad
                ·
                  exact fin15Anchored_clause26815 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26816 chi hbad
                ·
                  exact fin15Anchored_clause26817 chi hbad
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
                exact fin15Anchored_clause26818 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26819 chi hbad
                ·
                  exact fin15Anchored_clause26820 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26821 chi hbad
                ·
                  exact fin15Anchored_clause26822 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26823 chi hbad
                ·
                  exact fin15Anchored_clause26824 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26825 chi hbad
                ·
                  exact fin15Anchored_clause26826 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26827 chi hbad
                ·
                  exact fin15Anchored_clause26828 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26829 chi hbad
                ·
                  exact fin15Anchored_clause26830 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26831 chi hbad
                ·
                  exact fin15Anchored_clause26832 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26833 chi hbad
                ·
                  exact fin15Anchored_clause26834 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26835 chi hbad
                ·
                  exact fin15Anchored_clause26836 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26837 chi hbad
                ·
                  exact fin15Anchored_clause26838 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26839 chi hbad
                ·
                  exact fin15Anchored_clause26840 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26841 chi hbad
                ·
                  exact fin15Anchored_clause26842 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26843 chi hbad
                ·
                  exact fin15Anchored_clause26844 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26845 chi hbad
                ·
                  exact fin15Anchored_clause26846 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26847 chi hbad
                ·
                  exact fin15Anchored_clause26848 chi hbad
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
                  exact fin15Anchored_clause26849 chi hbad
                ·
                  exact fin15Anchored_clause26850 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26851 chi hbad
                ·
                  exact fin15Anchored_clause26852 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26853 chi hbad
                ·
                  exact fin15Anchored_clause26854 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26855 chi hbad
                ·
                  exact fin15Anchored_clause26856 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26857 chi hbad
                ·
                  exact fin15Anchored_clause26858 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26859 chi hbad
                ·
                  exact fin15Anchored_clause26860 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26861 chi hbad
                ·
                  exact fin15Anchored_clause26862 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26863 chi hbad
                ·
                  exact fin15Anchored_clause26864 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26865 chi hbad
                ·
                  exact fin15Anchored_clause26866 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26867 chi hbad
                ·
                  exact fin15Anchored_clause26868 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26869 chi hbad
                ·
                  exact fin15Anchored_clause26870 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26871 chi hbad
                ·
                  exact fin15Anchored_clause26872 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26873 chi hbad
                ·
                  exact fin15Anchored_clause26874 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26875 chi hbad
                ·
                  exact fin15Anchored_clause26876 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26877 chi hbad
                ·
                  exact fin15Anchored_clause26878 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26879 chi hbad
                ·
                  exact fin15Anchored_clause26880 chi hbad
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
                exact fin15Anchored_clause26881 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26882 chi hbad
                ·
                  exact fin15Anchored_clause26883 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26884 chi hbad
                ·
                  exact fin15Anchored_clause26885 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26886 chi hbad
                ·
                  exact fin15Anchored_clause26887 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26888 chi hbad
                ·
                  exact fin15Anchored_clause26889 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26890 chi hbad
                ·
                  exact fin15Anchored_clause26891 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26892 chi hbad
                ·
                  exact fin15Anchored_clause26893 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26894 chi hbad
                ·
                  exact fin15Anchored_clause26895 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26896 chi hbad
                ·
                  exact fin15Anchored_clause26897 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26898 chi hbad
                ·
                  exact fin15Anchored_clause26899 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26900 chi hbad
                ·
                  exact fin15Anchored_clause26901 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26902 chi hbad
                ·
                  exact fin15Anchored_clause26903 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26904 chi hbad
                ·
                  exact fin15Anchored_clause26905 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26906 chi hbad
                ·
                  exact fin15Anchored_clause26907 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26908 chi hbad
                ·
                  exact fin15Anchored_clause26909 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26910 chi hbad
                ·
                  exact fin15Anchored_clause26911 chi hbad
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
                  exact fin15Anchored_clause26912 chi hbad
                ·
                  exact fin15Anchored_clause26913 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26914 chi hbad
                ·
                  exact fin15Anchored_clause26915 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26916 chi hbad
                ·
                  exact fin15Anchored_clause26917 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26918 chi hbad
                ·
                  exact fin15Anchored_clause26919 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26920 chi hbad
                ·
                  exact fin15Anchored_clause26921 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26922 chi hbad
                ·
                  exact fin15Anchored_clause26923 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26924 chi hbad
                ·
                  exact fin15Anchored_clause26925 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26926 chi hbad
                ·
                  exact fin15Anchored_clause26927 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26928 chi hbad
                ·
                  exact fin15Anchored_clause26929 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26930 chi hbad
                ·
                  exact fin15Anchored_clause26931 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26932 chi hbad
                ·
                  exact fin15Anchored_clause26933 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26934 chi hbad
                ·
                  exact fin15Anchored_clause26935 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26936 chi hbad
                ·
                  exact fin15Anchored_clause26937 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26938 chi hbad
                ·
                  exact fin15Anchored_clause26939 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26940 chi hbad
                ·
                  exact fin15Anchored_clause26941 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26942 chi hbad
                ·
                  exact fin15Anchored_clause26943 chi hbad
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
                exact fin15Anchored_clause26944 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26945 chi hbad
                ·
                  exact fin15Anchored_clause26946 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26947 chi hbad
                ·
                  exact fin15Anchored_clause26948 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26949 chi hbad
                ·
                  exact fin15Anchored_clause26950 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26951 chi hbad
                ·
                  exact fin15Anchored_clause26952 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26953 chi hbad
                ·
                  exact fin15Anchored_clause26954 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26955 chi hbad
                ·
                  exact fin15Anchored_clause26956 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26957 chi hbad
                ·
                  exact fin15Anchored_clause26958 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26959 chi hbad
                ·
                  exact fin15Anchored_clause26960 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26961 chi hbad
                ·
                  exact fin15Anchored_clause26962 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26963 chi hbad
                ·
                  exact fin15Anchored_clause26964 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26965 chi hbad
                ·
                  exact fin15Anchored_clause26966 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26967 chi hbad
                ·
                  exact fin15Anchored_clause26968 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26969 chi hbad
                ·
                  exact fin15Anchored_clause26970 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26971 chi hbad
                ·
                  exact fin15Anchored_clause26972 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26973 chi hbad
                ·
                  exact fin15Anchored_clause26974 chi hbad
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
                  exact fin15Anchored_clause26975 chi hbad
                ·
                  exact fin15Anchored_clause26976 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26977 chi hbad
                ·
                  exact fin15Anchored_clause26978 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26979 chi hbad
                ·
                  exact fin15Anchored_clause26980 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26981 chi hbad
                ·
                  exact fin15Anchored_clause26982 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26983 chi hbad
                ·
                  exact fin15Anchored_clause26984 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26985 chi hbad
                ·
                  exact fin15Anchored_clause26986 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26987 chi hbad
                ·
                  exact fin15Anchored_clause26988 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26989 chi hbad
                ·
                  exact fin15Anchored_clause26990 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26991 chi hbad
                ·
                  exact fin15Anchored_clause26992 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26993 chi hbad
                ·
                  exact fin15Anchored_clause26994 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26995 chi hbad
                ·
                  exact fin15Anchored_clause26996 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26997 chi hbad
                ·
                  exact fin15Anchored_clause26998 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause26999 chi hbad
                ·
                  exact fin15Anchored_clause27000 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27001 chi hbad
                ·
                  exact fin15Anchored_clause27002 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27003 chi hbad
                ·
                  exact fin15Anchored_clause27004 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27005 chi hbad
                ·
                  exact fin15Anchored_clause27006 chi hbad

end ErdosSzekeres

end
