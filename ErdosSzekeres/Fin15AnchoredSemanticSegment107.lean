module

public import ErdosSzekeres.Fin15AnchoredClauseChunk210
public import ErdosSzekeres.Fin15AnchoredClauseChunk211
public import ErdosSzekeres.Fin15AnchoredClauseChunk212

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 107. -/

theorem fin15Anchored_rejectSemanticSegment107
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom4498 chi ∧
      Fin15AnchoredAtom1549 chi ∧
      Fin15AnchoredAtom1550 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1607 chi ∧
      Fin15AnchoredAtom1747 chi) ∨
      ((Fin15AnchoredAtom4499 chi ∧
      ¬Fin15AnchoredAtom1549 chi) ∨
      (Fin15AnchoredAtom4499 chi ∧
      ¬Fin15AnchoredAtom1553 chi))) ∨
      (((Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom1552 chi) ∨
      (Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom1553 chi)) ∨
      ((Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom1554 chi) ∨
      (Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom1610 chi)))) ∨
      ((((Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom1750 chi) ∨
      (¬Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1750 chi)) ∨
      ((Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom1555 chi) ∨
      (Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom1556 chi))) ∨
      (((Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom1561 chi) ∨
      (Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom1576 chi)) ∨
      ((Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom1751 chi) ∨
      (¬Fin15AnchoredAtom4502 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1576 chi ∧
      Fin15AnchoredAtom1751 chi))))) ∨
      (((((Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom1555 chi) ∨
      (Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom1558 chi)) ∨
      ((Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom1563 chi) ∨
      (Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom1578 chi))) ∨
      (((Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom1753 chi) ∨
      (¬Fin15AnchoredAtom4504 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1753 chi)) ∨
      ((Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom1555 chi) ∨
      (Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom1559 chi)))) ∨
      ((((Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom1564 chi) ∨
      (Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom1579 chi)) ∨
      ((Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom1754 chi) ∨
      (¬Fin15AnchoredAtom4505 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1754 chi))) ∨
      (((Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom1555 chi) ∨
      (Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom1560 chi)) ∨
      ((Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom1565 chi) ∨
      (Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom1580 chi)))))) ∨
      ((((((Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom1755 chi) ∨
      (¬Fin15AnchoredAtom4506 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1580 chi ∧
      Fin15AnchoredAtom1755 chi)) ∨
      ((Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom1556 chi) ∨
      (Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom1558 chi))) ∨
      (((Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom1567 chi) ∨
      (Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom1582 chi)) ∨
      ((Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom1757 chi) ∨
      (¬Fin15AnchoredAtom4508 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1757 chi)))) ∨
      ((((Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom1556 chi) ∨
      (Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom1559 chi)) ∨
      ((Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom1568 chi) ∨
      (Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom1583 chi))) ∨
      (((Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom1758 chi) ∨
      (¬Fin15AnchoredAtom4509 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1758 chi)) ∨
      ((Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom1556 chi) ∨
      (Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom1560 chi))))) ∨
      (((((Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom1569 chi) ∨
      (Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom1584 chi)) ∨
      ((Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom1759 chi) ∨
      (¬Fin15AnchoredAtom4510 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1584 chi ∧
      Fin15AnchoredAtom1759 chi))) ∨
      (((Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom1558 chi) ∨
      (Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom1559 chi)) ∨
      ((Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom1588 chi)))) ∨
      ((((Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom1763 chi) ∨
      (¬Fin15AnchoredAtom4514 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1763 chi)) ∨
      ((Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom1558 chi) ∨
      (Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom1560 chi))) ∨
      (((Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom1574 chi) ∨
      (Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom1589 chi)) ∨
      ((Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom1764 chi) ∨
      (¬Fin15AnchoredAtom4515 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1764 chi))))))) ∨
      ((((((Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom1559 chi) ∨
      ((Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom1560 chi) ∨
      (Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom1575 chi))) ∨
      (((Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom1590 chi) ∨
      (Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom1765 chi)) ∨
      ((¬Fin15AnchoredAtom4516 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1765 chi) ∨
      (Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom1561 chi)))) ∨
      ((((Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom1562 chi) ∨
      (Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom1566 chi)) ∨
      ((Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom1766 chi) ∨
      (¬Fin15AnchoredAtom4517 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1562 chi ∧
      Fin15AnchoredAtom1566 chi ∧
      Fin15AnchoredAtom1591 chi ∧
      Fin15AnchoredAtom1766 chi))) ∨
      (((Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom1561 chi) ∨
      (Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom1563 chi)) ∨
      ((Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom1567 chi) ∨
      (Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom1592 chi))))) ∨
      (((((Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom1767 chi) ∨
      (¬Fin15AnchoredAtom4518 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1767 chi)) ∨
      ((Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom1561 chi) ∨
      (Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom1564 chi))) ∨
      (((Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom1568 chi) ∨
      (Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom1593 chi)) ∨
      ((Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom1768 chi) ∨
      (¬Fin15AnchoredAtom4519 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1768 chi)))) ∨
      ((((Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom1561 chi) ∨
      (Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom1565 chi)) ∨
      ((Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom1569 chi) ∨
      (Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom1594 chi))) ∨
      (((Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom1769 chi) ∨
      (¬Fin15AnchoredAtom4520 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1594 chi ∧
      Fin15AnchoredAtom1769 chi)) ∨
      ((Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom1563 chi) ∨
      (Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom1595 chi)))))) ∨
      ((((((Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom1770 chi) ∨
      (¬Fin15AnchoredAtom4521 chi ∧
      Fin15AnchoredAtom1562 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1595 chi ∧
      Fin15AnchoredAtom1770 chi)) ∨
      ((Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom1564 chi) ∨
      (Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom1596 chi))) ∨
      (((Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom1771 chi) ∨
      (Fin15AnchoredAtom4523 chi ∧
      ¬Fin15AnchoredAtom1562 chi)) ∨
      ((Fin15AnchoredAtom4523 chi ∧
      ¬Fin15AnchoredAtom1565 chi) ∨
      (Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom1563 chi)))) ∨
      ((((Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom1564 chi) ∨
      (Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom1573 chi)) ∨
      ((Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom1598 chi) ∨
      (Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom1773 chi))) ∨
      (((¬Fin15AnchoredAtom4524 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1773 chi) ∨
      (Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom1563 chi)) ∨
      ((Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom1565 chi) ∨
      (Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom1574 chi))))) ∨
      (((((Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom1599 chi) ∨
      (Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom1774 chi)) ∨
      ((¬Fin15AnchoredAtom4525 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1774 chi) ∨
      (Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom1564 chi))) ∨
      (((Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom1565 chi) ∨
      (Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom1575 chi)) ∨
      ((Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom1600 chi) ∨
      (Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom1775 chi)))) ∨
      ((((¬Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1775 chi) ∨
      (Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom1567 chi)) ∨
      ((Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom1601 chi) ∨
      (Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom1776 chi))) ∨
      (((¬Fin15AnchoredAtom4527 chi ∧
      Fin15AnchoredAtom1566 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1601 chi ∧
      Fin15AnchoredAtom1776 chi) ∨
      (Fin15AnchoredAtom4528 chi ∧
      ¬Fin15AnchoredAtom1568 chi)) ∨
      ((Fin15AnchoredAtom4528 chi ∧
      ¬Fin15AnchoredAtom1602 chi) ∨
      (¬Fin15AnchoredAtom4528 chi ∧
      Fin15AnchoredAtom1566 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1571 chi ∧
      Fin15AnchoredAtom1602 chi ∧
      Fin15AnchoredAtom1777 chi)))))))) ∨
      (((((((Fin15AnchoredAtom4529 chi ∧
      ¬Fin15AnchoredAtom1566 chi) ∨
      ((Fin15AnchoredAtom4529 chi ∧
      ¬Fin15AnchoredAtom1603 chi) ∨
      (Fin15AnchoredAtom4529 chi ∧
      ¬Fin15AnchoredAtom1778 chi))) ∨
      (((Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom1567 chi) ∨
      (Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom1568 chi)) ∨
      ((Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom1604 chi)))) ∨
      ((((Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom1779 chi) ∨
      (¬Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1779 chi)) ∨
      ((Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom1567 chi) ∨
      (Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom1569 chi))) ∨
      (((Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom1574 chi) ∨
      (Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom1605 chi)) ∨
      ((Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom1780 chi) ∨
      (¬Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1780 chi))))) ∨
      (((((Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom1568 chi) ∨
      (Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom1569 chi)) ∨
      ((Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom1575 chi) ∨
      (Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom1606 chi))) ∨
      (((Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom1781 chi) ∨
      (¬Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1781 chi)) ∨
      ((Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom1607 chi)))) ∨
      ((((Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom1782 chi) ∨
      (¬Fin15AnchoredAtom4533 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1571 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1607 chi ∧
      Fin15AnchoredAtom1782 chi)) ∨
      ((Fin15AnchoredAtom4534 chi ∧
      ¬Fin15AnchoredAtom1570 chi) ∨
      (Fin15AnchoredAtom4534 chi ∧
      ¬Fin15AnchoredAtom1574 chi))) ∨
      (((Fin15AnchoredAtom4534 chi ∧
      ¬Fin15AnchoredAtom1608 chi) ∨
      (¬Fin15AnchoredAtom4534 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1572 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1608 chi ∧
      Fin15AnchoredAtom1783 chi)) ∨
      ((Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom1574 chi)))))) ∨
      ((((((Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom1575 chi) ∨
      (Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom1610 chi)) ∨
      ((Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom1785 chi) ∨
      (¬Fin15AnchoredAtom4536 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1785 chi))) ∨
      (((Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom1576 chi) ∨
      (Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom1578 chi)) ∨
      ((Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom1582 chi) ∨
      (Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom1592 chi)))) ∨
      ((((Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom1787 chi) ∨
      (¬Fin15AnchoredAtom4538 chi ∧
      Fin15AnchoredAtom1576 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1787 chi)) ∨
      ((Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom1576 chi) ∨
      (Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom1579 chi))) ∨
      (((Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom1583 chi) ∨
      (Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom1593 chi)) ∨
      ((Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom1788 chi) ∨
      (¬Fin15AnchoredAtom4539 chi ∧
      Fin15AnchoredAtom1576 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1788 chi))))) ∨
      (((((Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom1576 chi) ∨
      (Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom1580 chi)) ∨
      ((Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom1584 chi) ∨
      (Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom1594 chi))) ∨
      (((Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom1789 chi) ∨
      (Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom1578 chi)) ∨
      ((Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom1579 chi) ∨
      (Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom1588 chi)))) ∨
      ((((Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom1598 chi) ∨
      (Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom1793 chi)) ∨
      ((¬Fin15AnchoredAtom4544 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1793 chi) ∨
      (Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom1578 chi))) ∨
      (((Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom1580 chi) ∨
      (Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom1589 chi)) ∨
      ((Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom1599 chi) ∨
      (Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom1794 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom4545 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1580 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1794 chi) ∨
      (Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom1579 chi)) ∨
      ((Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom1580 chi) ∨
      (Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom1590 chi))) ∨
      (((Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom1600 chi) ∨
      (Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom1795 chi)) ∨
      ((¬Fin15AnchoredAtom4546 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1580 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1795 chi) ∨
      (Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom1582 chi)))) ∨
      ((((Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom1583 chi) ∨
      (Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom1588 chi)) ∨
      ((Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom1604 chi) ∨
      (Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom1799 chi))) ∨
      (((¬Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1799 chi) ∨
      (Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom1582 chi)) ∨
      ((Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom1584 chi) ∨
      (Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom1589 chi))))) ∨
      (((((Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom1605 chi) ∨
      (Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom1800 chi)) ∨
      ((¬Fin15AnchoredAtom4551 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1584 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1800 chi) ∨
      (Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom1583 chi))) ∨
      (((Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom1584 chi) ∨
      (Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom1590 chi)) ∨
      ((Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom1606 chi) ∨
      (Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom1801 chi)))) ∨
      ((((¬Fin15AnchoredAtom4552 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1584 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1801 chi) ∨
      (Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom1588 chi)) ∨
      ((Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom1589 chi) ∨
      (Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom1590 chi))) ∨
      (((Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom1610 chi) ∨
      (Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom1805 chi)) ∨
      ((¬Fin15AnchoredAtom4556 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1805 chi) ∨
      (Fin15AnchoredAtom4557 chi ∧
      ¬Fin15AnchoredAtom1592 chi)))))) ∨
      ((((((Fin15AnchoredAtom4557 chi ∧
      ¬Fin15AnchoredAtom1595 chi) ∨
      (Fin15AnchoredAtom4557 chi ∧
      ¬Fin15AnchoredAtom1601 chi)) ∨
      ((Fin15AnchoredAtom4558 chi ∧
      ¬Fin15AnchoredAtom1593 chi) ∨
      (Fin15AnchoredAtom4559 chi ∧
      ¬Fin15AnchoredAtom1594 chi))) ∨
      (((Fin15AnchoredAtom4559 chi ∧
      ¬Fin15AnchoredAtom1597 chi) ∨
      (Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom1592 chi)) ∨
      ((Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom1593 chi) ∨
      (Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom1598 chi)))) ∨
      ((((Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom1604 chi) ∨
      (Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom1809 chi)) ∨
      ((¬Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1809 chi) ∨
      (Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom1592 chi))) ∨
      (((Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom1594 chi) ∨
      (Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom1599 chi)) ∨
      ((Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom1605 chi) ∨
      (Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom1810 chi))))) ∨
      (((((¬Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1594 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1810 chi) ∨
      (Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom1593 chi)) ∨
      ((Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom1594 chi) ∨
      (Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom1600 chi))) ∨
      (((Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom1606 chi) ∨
      (Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom1811 chi)) ∨
      ((¬Fin15AnchoredAtom4562 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1594 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom4563 chi ∧
      ¬Fin15AnchoredAtom1598 chi)))) ∨
      ((((Fin15AnchoredAtom4564 chi ∧
      ¬Fin15AnchoredAtom1595 chi) ∨
      (Fin15AnchoredAtom4564 chi ∧
      ¬Fin15AnchoredAtom1599 chi)) ∨
      ((Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom1598 chi) ∨
      (Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom1599 chi))) ∨
      (((Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom1600 chi) ∨
      (Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom1610 chi)) ∨
      ((Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom1815 chi) ∨
      (¬Fin15AnchoredAtom4566 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1815 chi)))))))))) := by
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
                exact fin15Anchored_clause27007 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27008 chi hbad
                ·
                  exact fin15Anchored_clause27009 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27010 chi hbad
                ·
                  exact fin15Anchored_clause27011 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27012 chi hbad
                ·
                  exact fin15Anchored_clause27013 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27014 chi hbad
                ·
                  exact fin15Anchored_clause27015 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27016 chi hbad
                ·
                  exact fin15Anchored_clause27017 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27018 chi hbad
                ·
                  exact fin15Anchored_clause27019 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27020 chi hbad
                ·
                  exact fin15Anchored_clause27021 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27022 chi hbad
                ·
                  exact fin15Anchored_clause27023 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27024 chi hbad
                ·
                  exact fin15Anchored_clause27025 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27026 chi hbad
                ·
                  exact fin15Anchored_clause27027 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27028 chi hbad
                ·
                  exact fin15Anchored_clause27029 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27030 chi hbad
                ·
                  exact fin15Anchored_clause27031 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27032 chi hbad
                ·
                  exact fin15Anchored_clause27033 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27034 chi hbad
                ·
                  exact fin15Anchored_clause27035 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27036 chi hbad
                ·
                  exact fin15Anchored_clause27037 chi hbad
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
                  exact fin15Anchored_clause27038 chi hbad
                ·
                  exact fin15Anchored_clause27039 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27040 chi hbad
                ·
                  exact fin15Anchored_clause27041 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27042 chi hbad
                ·
                  exact fin15Anchored_clause27043 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27044 chi hbad
                ·
                  exact fin15Anchored_clause27045 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27046 chi hbad
                ·
                  exact fin15Anchored_clause27047 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27048 chi hbad
                ·
                  exact fin15Anchored_clause27049 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27050 chi hbad
                ·
                  exact fin15Anchored_clause27051 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27052 chi hbad
                ·
                  exact fin15Anchored_clause27053 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27054 chi hbad
                ·
                  exact fin15Anchored_clause27055 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27056 chi hbad
                ·
                  exact fin15Anchored_clause27057 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27058 chi hbad
                ·
                  exact fin15Anchored_clause27059 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27060 chi hbad
                ·
                  exact fin15Anchored_clause27061 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27062 chi hbad
                ·
                  exact fin15Anchored_clause27063 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27064 chi hbad
                ·
                  exact fin15Anchored_clause27065 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27066 chi hbad
                ·
                  exact fin15Anchored_clause27067 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27068 chi hbad
                ·
                  exact fin15Anchored_clause27069 chi hbad
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
                exact fin15Anchored_clause27070 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27071 chi hbad
                ·
                  exact fin15Anchored_clause27072 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27073 chi hbad
                ·
                  exact fin15Anchored_clause27074 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27075 chi hbad
                ·
                  exact fin15Anchored_clause27076 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27077 chi hbad
                ·
                  exact fin15Anchored_clause27078 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27079 chi hbad
                ·
                  exact fin15Anchored_clause27080 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27081 chi hbad
                ·
                  exact fin15Anchored_clause27082 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27083 chi hbad
                ·
                  exact fin15Anchored_clause27084 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27085 chi hbad
                ·
                  exact fin15Anchored_clause27086 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27087 chi hbad
                ·
                  exact fin15Anchored_clause27088 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27089 chi hbad
                ·
                  exact fin15Anchored_clause27090 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27091 chi hbad
                ·
                  exact fin15Anchored_clause27092 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27093 chi hbad
                ·
                  exact fin15Anchored_clause27094 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27095 chi hbad
                ·
                  exact fin15Anchored_clause27096 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27097 chi hbad
                ·
                  exact fin15Anchored_clause27098 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27099 chi hbad
                ·
                  exact fin15Anchored_clause27100 chi hbad
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
                  exact fin15Anchored_clause27101 chi hbad
                ·
                  exact fin15Anchored_clause27102 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27103 chi hbad
                ·
                  exact fin15Anchored_clause27104 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27105 chi hbad
                ·
                  exact fin15Anchored_clause27106 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27107 chi hbad
                ·
                  exact fin15Anchored_clause27108 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27109 chi hbad
                ·
                  exact fin15Anchored_clause27110 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27111 chi hbad
                ·
                  exact fin15Anchored_clause27112 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27113 chi hbad
                ·
                  exact fin15Anchored_clause27114 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27115 chi hbad
                ·
                  exact fin15Anchored_clause27116 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27117 chi hbad
                ·
                  exact fin15Anchored_clause27118 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27119 chi hbad
                ·
                  exact fin15Anchored_clause27120 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27121 chi hbad
                ·
                  exact fin15Anchored_clause27122 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27123 chi hbad
                ·
                  exact fin15Anchored_clause27124 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27125 chi hbad
                ·
                  exact fin15Anchored_clause27126 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27127 chi hbad
                ·
                  exact fin15Anchored_clause27128 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27129 chi hbad
                ·
                  exact fin15Anchored_clause27130 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27131 chi hbad
                ·
                  exact fin15Anchored_clause27132 chi hbad
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
                exact fin15Anchored_clause27133 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27134 chi hbad
                ·
                  exact fin15Anchored_clause27135 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27136 chi hbad
                ·
                  exact fin15Anchored_clause27137 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27138 chi hbad
                ·
                  exact fin15Anchored_clause27139 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27140 chi hbad
                ·
                  exact fin15Anchored_clause27141 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27142 chi hbad
                ·
                  exact fin15Anchored_clause27143 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27144 chi hbad
                ·
                  exact fin15Anchored_clause27145 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27146 chi hbad
                ·
                  exact fin15Anchored_clause27147 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27148 chi hbad
                ·
                  exact fin15Anchored_clause27149 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27150 chi hbad
                ·
                  exact fin15Anchored_clause27151 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27152 chi hbad
                ·
                  exact fin15Anchored_clause27153 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27154 chi hbad
                ·
                  exact fin15Anchored_clause27155 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27156 chi hbad
                ·
                  exact fin15Anchored_clause27157 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27158 chi hbad
                ·
                  exact fin15Anchored_clause27159 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27160 chi hbad
                ·
                  exact fin15Anchored_clause27161 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27162 chi hbad
                ·
                  exact fin15Anchored_clause27163 chi hbad
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
                  exact fin15Anchored_clause27164 chi hbad
                ·
                  exact fin15Anchored_clause27165 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27166 chi hbad
                ·
                  exact fin15Anchored_clause27167 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27168 chi hbad
                ·
                  exact fin15Anchored_clause27169 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27170 chi hbad
                ·
                  exact fin15Anchored_clause27171 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27172 chi hbad
                ·
                  exact fin15Anchored_clause27173 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27174 chi hbad
                ·
                  exact fin15Anchored_clause27175 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27176 chi hbad
                ·
                  exact fin15Anchored_clause27177 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27178 chi hbad
                ·
                  exact fin15Anchored_clause27179 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27180 chi hbad
                ·
                  exact fin15Anchored_clause27181 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27182 chi hbad
                ·
                  exact fin15Anchored_clause27183 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27184 chi hbad
                ·
                  exact fin15Anchored_clause27185 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27186 chi hbad
                ·
                  exact fin15Anchored_clause27187 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27188 chi hbad
                ·
                  exact fin15Anchored_clause27189 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27190 chi hbad
                ·
                  exact fin15Anchored_clause27191 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27192 chi hbad
                ·
                  exact fin15Anchored_clause27193 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27194 chi hbad
                ·
                  exact fin15Anchored_clause27195 chi hbad
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
                  exact fin15Anchored_clause27196 chi hbad
                ·
                  exact fin15Anchored_clause27197 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27198 chi hbad
                ·
                  exact fin15Anchored_clause27199 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27200 chi hbad
                ·
                  exact fin15Anchored_clause27201 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27202 chi hbad
                ·
                  exact fin15Anchored_clause27203 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27204 chi hbad
                ·
                  exact fin15Anchored_clause27205 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27206 chi hbad
                ·
                  exact fin15Anchored_clause27207 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27208 chi hbad
                ·
                  exact fin15Anchored_clause27209 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27210 chi hbad
                ·
                  exact fin15Anchored_clause27211 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27212 chi hbad
                ·
                  exact fin15Anchored_clause27213 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27214 chi hbad
                ·
                  exact fin15Anchored_clause27215 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27216 chi hbad
                ·
                  exact fin15Anchored_clause27217 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27218 chi hbad
                ·
                  exact fin15Anchored_clause27219 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27220 chi hbad
                ·
                  exact fin15Anchored_clause27221 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27222 chi hbad
                ·
                  exact fin15Anchored_clause27223 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27224 chi hbad
                ·
                  exact fin15Anchored_clause27225 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27226 chi hbad
                ·
                  exact fin15Anchored_clause27227 chi hbad
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
                  exact fin15Anchored_clause27228 chi hbad
                ·
                  exact fin15Anchored_clause27229 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27230 chi hbad
                ·
                  exact fin15Anchored_clause27231 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27232 chi hbad
                ·
                  exact fin15Anchored_clause27233 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27234 chi hbad
                ·
                  exact fin15Anchored_clause27235 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27236 chi hbad
                ·
                  exact fin15Anchored_clause27237 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27238 chi hbad
                ·
                  exact fin15Anchored_clause27239 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27240 chi hbad
                ·
                  exact fin15Anchored_clause27241 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27242 chi hbad
                ·
                  exact fin15Anchored_clause27243 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27244 chi hbad
                ·
                  exact fin15Anchored_clause27245 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27246 chi hbad
                ·
                  exact fin15Anchored_clause27247 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27248 chi hbad
                ·
                  exact fin15Anchored_clause27249 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27250 chi hbad
                ·
                  exact fin15Anchored_clause27251 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27252 chi hbad
                ·
                  exact fin15Anchored_clause27253 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27254 chi hbad
                ·
                  exact fin15Anchored_clause27255 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27256 chi hbad
                ·
                  exact fin15Anchored_clause27257 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27258 chi hbad
                ·
                  exact fin15Anchored_clause27259 chi hbad

end ErdosSzekeres

end
