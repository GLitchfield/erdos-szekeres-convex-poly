module

public import ErdosSzekeres.Fin15AnchoredClauseChunk212
public import ErdosSzekeres.Fin15AnchoredClauseChunk213
public import ErdosSzekeres.Fin15AnchoredClauseChunk214

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 108. -/

theorem fin15Anchored_rejectSemanticSegment108
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom4567 chi ∧
      ¬Fin15AnchoredAtom1604 chi) ∨
      ((Fin15AnchoredAtom4567 chi ∧
      ¬Fin15AnchoredAtom1816 chi) ∨
      (¬Fin15AnchoredAtom4567 chi ∧
      Fin15AnchoredAtom1601 chi ∧
      Fin15AnchoredAtom1602 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1607 chi ∧
      Fin15AnchoredAtom1816 chi))) ∨
      (((Fin15AnchoredAtom4568 chi ∧
      ¬Fin15AnchoredAtom1817 chi) ∨
      (¬Fin15AnchoredAtom4568 chi ∧
      Fin15AnchoredAtom1601 chi ∧
      Fin15AnchoredAtom1603 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1608 chi ∧
      Fin15AnchoredAtom1817 chi)) ∨
      ((Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom1604 chi) ∨
      (Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom1605 chi)))) ∨
      ((((Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom1606 chi) ∨
      (Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom1610 chi)) ∨
      ((Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom1819 chi) ∨
      (¬Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1819 chi))) ∨
      (((Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom1611 chi) ∨
      (Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom1612 chi)) ∨
      ((Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom1618 chi) ∨
      (Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom1639 chi))))) ∨
      (((((Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom1695 chi) ∨
      (¬Fin15AnchoredAtom4572 chi ∧
      Fin15AnchoredAtom1611 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1618 chi ∧
      Fin15AnchoredAtom1639 chi ∧
      Fin15AnchoredAtom1695 chi)) ∨
      ((Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom1611 chi) ∨
      (Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom1613 chi))) ∨
      (((Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom1619 chi) ∨
      (Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom1640 chi)) ∨
      ((Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom1696 chi) ∨
      (¬Fin15AnchoredAtom4573 chi ∧
      Fin15AnchoredAtom1611 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1619 chi ∧
      Fin15AnchoredAtom1640 chi ∧
      Fin15AnchoredAtom1696 chi)))) ∨
      ((((Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom1611 chi) ∨
      (Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom1615 chi)) ∨
      ((Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom1621 chi) ∨
      (Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom1642 chi))) ∨
      (((Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (¬Fin15AnchoredAtom4575 chi ∧
      Fin15AnchoredAtom1611 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1621 chi ∧
      Fin15AnchoredAtom1642 chi ∧
      Fin15AnchoredAtom1698 chi)) ∨
      ((Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom1611 chi) ∨
      (Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom1616 chi)))))) ∨
      ((((((Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom1622 chi) ∨
      (Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom1643 chi)) ∨
      ((Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom1699 chi) ∨
      (¬Fin15AnchoredAtom4576 chi ∧
      Fin15AnchoredAtom1611 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1622 chi ∧
      Fin15AnchoredAtom1643 chi ∧
      Fin15AnchoredAtom1699 chi))) ∨
      (((Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom1611 chi) ∨
      (Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom1617 chi)) ∨
      ((Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom1623 chi) ∨
      (Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom1644 chi)))) ∨
      ((((Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom1700 chi) ∨
      (¬Fin15AnchoredAtom4577 chi ∧
      Fin15AnchoredAtom1611 chi ∧
      Fin15AnchoredAtom1617 chi ∧
      Fin15AnchoredAtom1623 chi ∧
      Fin15AnchoredAtom1644 chi ∧
      Fin15AnchoredAtom1700 chi)) ∨
      ((Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom1612 chi) ∨
      (Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom1613 chi))) ∨
      (((Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom1624 chi) ∨
      (Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom1645 chi)) ∨
      ((Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom1701 chi) ∨
      (¬Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1701 chi))))) ∨
      (((((Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom1612 chi) ∨
      (Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom1625 chi)) ∨
      ((Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom1646 chi) ∨
      (Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom1702 chi))) ∨
      (((¬Fin15AnchoredAtom4579 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1614 chi ∧
      Fin15AnchoredAtom1625 chi ∧
      Fin15AnchoredAtom1646 chi ∧
      Fin15AnchoredAtom1702 chi) ∨
      (Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom1612 chi)) ∨
      ((Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom1615 chi) ∨
      (Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom1626 chi)))) ∨
      ((((Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom1647 chi) ∨
      (Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom1703 chi)) ∨
      ((¬Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1703 chi) ∨
      (Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom1612 chi))) ∨
      (((Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom1616 chi) ∨
      (Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom1627 chi)) ∨
      ((Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom1648 chi) ∨
      (Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom1704 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom4581 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1627 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1704 chi) ∨
      ((Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom1612 chi) ∨
      (Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom1617 chi))) ∨
      (((Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom1628 chi) ∨
      (Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom1649 chi)) ∨
      ((Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom1705 chi) ∨
      (¬Fin15AnchoredAtom4582 chi ∧
      Fin15AnchoredAtom1612 chi ∧
      Fin15AnchoredAtom1617 chi ∧
      Fin15AnchoredAtom1628 chi ∧
      Fin15AnchoredAtom1649 chi ∧
      Fin15AnchoredAtom1705 chi)))) ∨
      ((((Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom1613 chi) ∨
      (Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom1614 chi)) ∨
      ((Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom1629 chi) ∨
      (Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom1650 chi))) ∨
      (((Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom1706 chi) ∨
      (¬Fin15AnchoredAtom4583 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1614 chi ∧
      Fin15AnchoredAtom1629 chi ∧
      Fin15AnchoredAtom1650 chi ∧
      Fin15AnchoredAtom1706 chi)) ∨
      ((Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom1613 chi) ∨
      (Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom1615 chi))))) ∨
      (((((Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom1630 chi) ∨
      (Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom1651 chi)) ∨
      ((Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom1707 chi) ∨
      (¬Fin15AnchoredAtom4584 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1707 chi))) ∨
      (((Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom1613 chi) ∨
      (Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom1616 chi)) ∨
      ((Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom1631 chi) ∨
      (Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom1652 chi)))) ∨
      ((((Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom1708 chi) ∨
      (¬Fin15AnchoredAtom4585 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1708 chi)) ∨
      ((Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom1613 chi) ∨
      (Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom1617 chi))) ∨
      (((Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom1632 chi) ∨
      (Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom1653 chi)) ∨
      ((Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom1709 chi) ∨
      (¬Fin15AnchoredAtom4586 chi ∧
      Fin15AnchoredAtom1613 chi ∧
      Fin15AnchoredAtom1617 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1653 chi ∧
      Fin15AnchoredAtom1709 chi)))))) ∨
      ((((((Fin15AnchoredAtom4587 chi ∧
      ¬Fin15AnchoredAtom1615 chi) ∨
      (Fin15AnchoredAtom4587 chi ∧
      ¬Fin15AnchoredAtom1654 chi)) ∨
      ((¬Fin15AnchoredAtom4587 chi ∧
      Fin15AnchoredAtom1614 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1633 chi ∧
      Fin15AnchoredAtom1654 chi ∧
      Fin15AnchoredAtom1710 chi) ∨
      (Fin15AnchoredAtom4588 chi ∧
      ¬Fin15AnchoredAtom1614 chi))) ∨
      (((Fin15AnchoredAtom4588 chi ∧
      ¬Fin15AnchoredAtom1616 chi) ∨
      (¬Fin15AnchoredAtom4588 chi ∧
      Fin15AnchoredAtom1614 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1634 chi ∧
      Fin15AnchoredAtom1655 chi ∧
      Fin15AnchoredAtom1711 chi)) ∨
      ((Fin15AnchoredAtom4589 chi ∧
      ¬Fin15AnchoredAtom1617 chi) ∨
      (Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom1615 chi)))) ∨
      ((((Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom1616 chi) ∨
      (Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom1636 chi)) ∨
      ((Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom1657 chi) ∨
      (Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom1713 chi))) ∨
      (((¬Fin15AnchoredAtom4590 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1657 chi ∧
      Fin15AnchoredAtom1713 chi) ∨
      (Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom1615 chi)) ∨
      ((Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom1617 chi) ∨
      (Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom1637 chi))))) ∨
      (((((Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom1658 chi) ∨
      (Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom1714 chi)) ∨
      ((¬Fin15AnchoredAtom4591 chi ∧
      Fin15AnchoredAtom1615 chi ∧
      Fin15AnchoredAtom1617 chi ∧
      Fin15AnchoredAtom1637 chi ∧
      Fin15AnchoredAtom1658 chi ∧
      Fin15AnchoredAtom1714 chi) ∨
      (Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom1616 chi))) ∨
      (((Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom1617 chi) ∨
      (Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom1638 chi)) ∨
      ((Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom1659 chi) ∨
      (Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom1715 chi)))) ∨
      ((((¬Fin15AnchoredAtom4592 chi ∧
      Fin15AnchoredAtom1616 chi ∧
      Fin15AnchoredAtom1617 chi ∧
      Fin15AnchoredAtom1638 chi ∧
      Fin15AnchoredAtom1659 chi ∧
      Fin15AnchoredAtom1715 chi) ∨
      (Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom1618 chi)) ∨
      ((Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom1619 chi) ∨
      (Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom1624 chi))) ∨
      (((Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom1660 chi) ∨
      (Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom1716 chi)) ∨
      ((¬Fin15AnchoredAtom4593 chi ∧
      Fin15AnchoredAtom1618 chi ∧
      Fin15AnchoredAtom1619 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1660 chi ∧
      Fin15AnchoredAtom1716 chi) ∨
      (Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom1618 chi)))))))) ∨
      (((((((Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom1621 chi) ∨
      ((Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom1626 chi) ∨
      (Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom1662 chi))) ∨
      (((Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom1718 chi) ∨
      (¬Fin15AnchoredAtom4595 chi ∧
      Fin15AnchoredAtom1618 chi ∧
      Fin15AnchoredAtom1621 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1662 chi ∧
      Fin15AnchoredAtom1718 chi)) ∨
      ((Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom1618 chi) ∨
      (Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom1622 chi)))) ∨
      ((((Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom1627 chi) ∨
      (Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom1663 chi)) ∨
      ((Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom1719 chi) ∨
      (¬Fin15AnchoredAtom4596 chi ∧
      Fin15AnchoredAtom1618 chi ∧
      Fin15AnchoredAtom1622 chi ∧
      Fin15AnchoredAtom1627 chi ∧
      Fin15AnchoredAtom1663 chi ∧
      Fin15AnchoredAtom1719 chi))) ∨
      (((Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom1618 chi) ∨
      (Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom1623 chi)) ∨
      ((Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom1628 chi) ∨
      (Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom1664 chi))))) ∨
      (((((Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom1720 chi) ∨
      (¬Fin15AnchoredAtom4597 chi ∧
      Fin15AnchoredAtom1618 chi ∧
      Fin15AnchoredAtom1623 chi ∧
      Fin15AnchoredAtom1628 chi ∧
      Fin15AnchoredAtom1664 chi ∧
      Fin15AnchoredAtom1720 chi)) ∨
      ((Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom1619 chi) ∨
      (Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom1621 chi))) ∨
      (((Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom1630 chi) ∨
      (Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom1666 chi)) ∨
      ((Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom1722 chi) ∨
      (¬Fin15AnchoredAtom4599 chi ∧
      Fin15AnchoredAtom1619 chi ∧
      Fin15AnchoredAtom1621 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1666 chi ∧
      Fin15AnchoredAtom1722 chi)))) ∨
      ((((Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom1619 chi) ∨
      (Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom1622 chi)) ∨
      ((Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom1631 chi) ∨
      (Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom1667 chi))) ∨
      (((Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom1723 chi) ∨
      (¬Fin15AnchoredAtom4600 chi ∧
      Fin15AnchoredAtom1619 chi ∧
      Fin15AnchoredAtom1622 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1667 chi ∧
      Fin15AnchoredAtom1723 chi)) ∨
      ((Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom1619 chi) ∨
      (Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom1623 chi)))))) ∨
      ((((((Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom1632 chi) ∨
      (Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom1668 chi)) ∨
      ((Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom1724 chi) ∨
      (¬Fin15AnchoredAtom4601 chi ∧
      Fin15AnchoredAtom1619 chi ∧
      Fin15AnchoredAtom1623 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1668 chi ∧
      Fin15AnchoredAtom1724 chi))) ∨
      (((Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom1621 chi) ∨
      (Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom1622 chi)) ∨
      ((Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom1636 chi) ∨
      (Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom1672 chi)))) ∨
      ((((Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom1728 chi) ∨
      (¬Fin15AnchoredAtom4605 chi ∧
      Fin15AnchoredAtom1621 chi ∧
      Fin15AnchoredAtom1622 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1672 chi ∧
      Fin15AnchoredAtom1728 chi)) ∨
      ((Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom1621 chi) ∨
      (Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom1623 chi))) ∨
      (((Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom1637 chi) ∨
      (Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom1673 chi)) ∨
      ((Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom1729 chi) ∨
      (¬Fin15AnchoredAtom4606 chi ∧
      Fin15AnchoredAtom1621 chi ∧
      Fin15AnchoredAtom1623 chi ∧
      Fin15AnchoredAtom1637 chi ∧
      Fin15AnchoredAtom1673 chi ∧
      Fin15AnchoredAtom1729 chi))))) ∨
      (((((Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom1622 chi) ∨
      (Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom1638 chi)) ∨
      ((Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom1674 chi) ∨
      (Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom1730 chi))) ∨
      (((¬Fin15AnchoredAtom4607 chi ∧
      Fin15AnchoredAtom1622 chi ∧
      Fin15AnchoredAtom1623 chi ∧
      Fin15AnchoredAtom1638 chi ∧
      Fin15AnchoredAtom1674 chi ∧
      Fin15AnchoredAtom1730 chi) ∨
      (Fin15AnchoredAtom4608 chi ∧
      ¬Fin15AnchoredAtom1675 chi)) ∨
      ((Fin15AnchoredAtom4608 chi ∧
      ¬Fin15AnchoredAtom1731 chi) ∨
      (¬Fin15AnchoredAtom4608 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1625 chi ∧
      Fin15AnchoredAtom1629 chi ∧
      Fin15AnchoredAtom1675 chi ∧
      Fin15AnchoredAtom1731 chi)))) ∨
      ((((Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom1624 chi) ∨
      (Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom1626 chi)) ∨
      ((Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom1630 chi) ∨
      (Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom1676 chi))) ∨
      (((Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      (¬Fin15AnchoredAtom4609 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1732 chi)) ∨
      ((Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom1624 chi) ∨
      (Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom1627 chi))))))) ∨
      ((((((Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom1631 chi) ∨
      ((Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom1677 chi) ∨
      (Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom1733 chi))) ∨
      (((¬Fin15AnchoredAtom4610 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1627 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1677 chi ∧
      Fin15AnchoredAtom1733 chi) ∨
      (Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom1624 chi)) ∨
      ((Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom1628 chi) ∨
      (Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom1632 chi)))) ∨
      ((((Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom1678 chi) ∨
      (Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom1734 chi)) ∨
      ((¬Fin15AnchoredAtom4611 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1628 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1678 chi ∧
      Fin15AnchoredAtom1734 chi) ∨
      (Fin15AnchoredAtom4612 chi ∧
      ¬Fin15AnchoredAtom1626 chi))) ∨
      (((Fin15AnchoredAtom4612 chi ∧
      ¬Fin15AnchoredAtom1679 chi) ∨
      (Fin15AnchoredAtom4612 chi ∧
      ¬Fin15AnchoredAtom1735 chi)) ∨
      ((¬Fin15AnchoredAtom4612 chi ∧
      Fin15AnchoredAtom1625 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1633 chi ∧
      Fin15AnchoredAtom1679 chi ∧
      Fin15AnchoredAtom1735 chi) ∨
      (Fin15AnchoredAtom4613 chi ∧
      ¬Fin15AnchoredAtom1627 chi))))) ∨
      (((((Fin15AnchoredAtom4613 chi ∧
      ¬Fin15AnchoredAtom1680 chi) ∨
      (Fin15AnchoredAtom4613 chi ∧
      ¬Fin15AnchoredAtom1736 chi)) ∨
      ((Fin15AnchoredAtom4614 chi ∧
      ¬Fin15AnchoredAtom1737 chi) ∨
      (Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom1626 chi))) ∨
      (((Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom1627 chi) ∨
      (Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom1636 chi)) ∨
      ((Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom1682 chi) ∨
      (Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom1738 chi)))) ∨
      ((((¬Fin15AnchoredAtom4615 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1627 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1682 chi ∧
      Fin15AnchoredAtom1738 chi) ∨
      (Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom1626 chi)) ∨
      ((Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom1628 chi) ∨
      (Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom1637 chi))) ∨
      (((Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom1683 chi) ∨
      (Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom1739 chi)) ∨
      ((¬Fin15AnchoredAtom4616 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1628 chi ∧
      Fin15AnchoredAtom1637 chi ∧
      Fin15AnchoredAtom1683 chi ∧
      Fin15AnchoredAtom1739 chi) ∨
      (Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom1627 chi)))))) ∨
      ((((((Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom1628 chi) ∨
      (Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom1638 chi)) ∨
      ((Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom1684 chi) ∨
      (Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom1740 chi))) ∨
      (((¬Fin15AnchoredAtom4617 chi ∧
      Fin15AnchoredAtom1627 chi ∧
      Fin15AnchoredAtom1628 chi ∧
      Fin15AnchoredAtom1638 chi ∧
      Fin15AnchoredAtom1684 chi ∧
      Fin15AnchoredAtom1740 chi) ∨
      (Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom1629 chi)) ∨
      ((Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom1630 chi) ∨
      (Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom1685 chi)))) ∨
      ((((Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom1741 chi) ∨
      (¬Fin15AnchoredAtom4618 chi ∧
      Fin15AnchoredAtom1629 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1633 chi ∧
      Fin15AnchoredAtom1685 chi ∧
      Fin15AnchoredAtom1741 chi)) ∨
      ((Fin15AnchoredAtom4619 chi ∧
      ¬Fin15AnchoredAtom1631 chi) ∨
      (¬Fin15AnchoredAtom4619 chi ∧
      Fin15AnchoredAtom1629 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1634 chi ∧
      Fin15AnchoredAtom1686 chi ∧
      Fin15AnchoredAtom1742 chi))) ∨
      (((Fin15AnchoredAtom4620 chi ∧
      ¬Fin15AnchoredAtom1687 chi) ∨
      (Fin15AnchoredAtom4620 chi ∧
      ¬Fin15AnchoredAtom1743 chi)) ∨
      ((¬Fin15AnchoredAtom4620 chi ∧
      Fin15AnchoredAtom1629 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1635 chi ∧
      Fin15AnchoredAtom1687 chi ∧
      Fin15AnchoredAtom1743 chi) ∨
      (Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom1630 chi))))) ∨
      (((((Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom1631 chi) ∨
      (Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom1636 chi)) ∨
      ((Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom1744 chi))) ∨
      (((¬Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1744 chi) ∨
      (Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom1630 chi)) ∨
      ((Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom1632 chi) ∨
      (Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom1637 chi)))) ∨
      ((((Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom1689 chi) ∨
      (Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom1745 chi)) ∨
      ((¬Fin15AnchoredAtom4622 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1637 chi ∧
      Fin15AnchoredAtom1689 chi ∧
      Fin15AnchoredAtom1745 chi) ∨
      (Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom1631 chi))) ∨
      (((Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom1632 chi) ∨
      (Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom1638 chi)) ∨
      ((Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom1690 chi) ∨
      (Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom1746 chi)))))))))) := by
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
                exact fin15Anchored_clause27260 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27261 chi hbad
                ·
                  exact fin15Anchored_clause27262 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27263 chi hbad
                ·
                  exact fin15Anchored_clause27264 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27265 chi hbad
                ·
                  exact fin15Anchored_clause27266 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27267 chi hbad
                ·
                  exact fin15Anchored_clause27268 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27269 chi hbad
                ·
                  exact fin15Anchored_clause27270 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27271 chi hbad
                ·
                  exact fin15Anchored_clause27272 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27273 chi hbad
                ·
                  exact fin15Anchored_clause27274 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27275 chi hbad
                ·
                  exact fin15Anchored_clause27276 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27277 chi hbad
                ·
                  exact fin15Anchored_clause27278 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27279 chi hbad
                ·
                  exact fin15Anchored_clause27280 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27281 chi hbad
                ·
                  exact fin15Anchored_clause27282 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27283 chi hbad
                ·
                  exact fin15Anchored_clause27284 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27285 chi hbad
                ·
                  exact fin15Anchored_clause27286 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27287 chi hbad
                ·
                  exact fin15Anchored_clause27288 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27289 chi hbad
                ·
                  exact fin15Anchored_clause27290 chi hbad
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
                  exact fin15Anchored_clause27291 chi hbad
                ·
                  exact fin15Anchored_clause27292 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27293 chi hbad
                ·
                  exact fin15Anchored_clause27294 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27295 chi hbad
                ·
                  exact fin15Anchored_clause27296 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27297 chi hbad
                ·
                  exact fin15Anchored_clause27298 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27299 chi hbad
                ·
                  exact fin15Anchored_clause27300 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27301 chi hbad
                ·
                  exact fin15Anchored_clause27302 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27303 chi hbad
                ·
                  exact fin15Anchored_clause27304 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27305 chi hbad
                ·
                  exact fin15Anchored_clause27306 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27307 chi hbad
                ·
                  exact fin15Anchored_clause27308 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27309 chi hbad
                ·
                  exact fin15Anchored_clause27310 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27311 chi hbad
                ·
                  exact fin15Anchored_clause27312 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27313 chi hbad
                ·
                  exact fin15Anchored_clause27314 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27315 chi hbad
                ·
                  exact fin15Anchored_clause27316 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27317 chi hbad
                ·
                  exact fin15Anchored_clause27318 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27319 chi hbad
                ·
                  exact fin15Anchored_clause27320 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27321 chi hbad
                ·
                  exact fin15Anchored_clause27322 chi hbad
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
                exact fin15Anchored_clause27323 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27324 chi hbad
                ·
                  exact fin15Anchored_clause27325 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27326 chi hbad
                ·
                  exact fin15Anchored_clause27327 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27328 chi hbad
                ·
                  exact fin15Anchored_clause27329 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27330 chi hbad
                ·
                  exact fin15Anchored_clause27331 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27332 chi hbad
                ·
                  exact fin15Anchored_clause27333 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27334 chi hbad
                ·
                  exact fin15Anchored_clause27335 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27336 chi hbad
                ·
                  exact fin15Anchored_clause27337 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27338 chi hbad
                ·
                  exact fin15Anchored_clause27339 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27340 chi hbad
                ·
                  exact fin15Anchored_clause27341 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27342 chi hbad
                ·
                  exact fin15Anchored_clause27343 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27344 chi hbad
                ·
                  exact fin15Anchored_clause27345 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27346 chi hbad
                ·
                  exact fin15Anchored_clause27347 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27348 chi hbad
                ·
                  exact fin15Anchored_clause27349 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27350 chi hbad
                ·
                  exact fin15Anchored_clause27351 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27352 chi hbad
                ·
                  exact fin15Anchored_clause27353 chi hbad
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
                  exact fin15Anchored_clause27354 chi hbad
                ·
                  exact fin15Anchored_clause27355 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27356 chi hbad
                ·
                  exact fin15Anchored_clause27357 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27358 chi hbad
                ·
                  exact fin15Anchored_clause27359 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27360 chi hbad
                ·
                  exact fin15Anchored_clause27361 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27362 chi hbad
                ·
                  exact fin15Anchored_clause27363 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27364 chi hbad
                ·
                  exact fin15Anchored_clause27365 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27366 chi hbad
                ·
                  exact fin15Anchored_clause27367 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27368 chi hbad
                ·
                  exact fin15Anchored_clause27369 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27370 chi hbad
                ·
                  exact fin15Anchored_clause27371 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27372 chi hbad
                ·
                  exact fin15Anchored_clause27373 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27374 chi hbad
                ·
                  exact fin15Anchored_clause27375 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27376 chi hbad
                ·
                  exact fin15Anchored_clause27377 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27378 chi hbad
                ·
                  exact fin15Anchored_clause27379 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27380 chi hbad
                ·
                  exact fin15Anchored_clause27381 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27382 chi hbad
                ·
                  exact fin15Anchored_clause27383 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27384 chi hbad
                ·
                  exact fin15Anchored_clause27385 chi hbad
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
                exact fin15Anchored_clause27386 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27387 chi hbad
                ·
                  exact fin15Anchored_clause27388 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27389 chi hbad
                ·
                  exact fin15Anchored_clause27390 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27391 chi hbad
                ·
                  exact fin15Anchored_clause27392 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27393 chi hbad
                ·
                  exact fin15Anchored_clause27394 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27395 chi hbad
                ·
                  exact fin15Anchored_clause27396 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27397 chi hbad
                ·
                  exact fin15Anchored_clause27398 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27399 chi hbad
                ·
                  exact fin15Anchored_clause27400 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27401 chi hbad
                ·
                  exact fin15Anchored_clause27402 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27403 chi hbad
                ·
                  exact fin15Anchored_clause27404 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27405 chi hbad
                ·
                  exact fin15Anchored_clause27406 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27407 chi hbad
                ·
                  exact fin15Anchored_clause27408 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27409 chi hbad
                ·
                  exact fin15Anchored_clause27410 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27411 chi hbad
                ·
                  exact fin15Anchored_clause27412 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27413 chi hbad
                ·
                  exact fin15Anchored_clause27414 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27415 chi hbad
                ·
                  exact fin15Anchored_clause27416 chi hbad
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
                  exact fin15Anchored_clause27417 chi hbad
                ·
                  exact fin15Anchored_clause27418 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27419 chi hbad
                ·
                  exact fin15Anchored_clause27420 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27421 chi hbad
                ·
                  exact fin15Anchored_clause27422 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27423 chi hbad
                ·
                  exact fin15Anchored_clause27424 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27425 chi hbad
                ·
                  exact fin15Anchored_clause27426 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27427 chi hbad
                ·
                  exact fin15Anchored_clause27428 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27429 chi hbad
                ·
                  exact fin15Anchored_clause27430 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27431 chi hbad
                ·
                  exact fin15Anchored_clause27432 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27433 chi hbad
                ·
                  exact fin15Anchored_clause27434 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27435 chi hbad
                ·
                  exact fin15Anchored_clause27436 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27437 chi hbad
                ·
                  exact fin15Anchored_clause27438 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27439 chi hbad
                ·
                  exact fin15Anchored_clause27440 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27441 chi hbad
                ·
                  exact fin15Anchored_clause27442 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27443 chi hbad
                ·
                  exact fin15Anchored_clause27444 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27445 chi hbad
                ·
                  exact fin15Anchored_clause27446 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27447 chi hbad
                ·
                  exact fin15Anchored_clause27448 chi hbad
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
                exact fin15Anchored_clause27449 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27450 chi hbad
                ·
                  exact fin15Anchored_clause27451 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27452 chi hbad
                ·
                  exact fin15Anchored_clause27453 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27454 chi hbad
                ·
                  exact fin15Anchored_clause27455 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27456 chi hbad
                ·
                  exact fin15Anchored_clause27457 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27458 chi hbad
                ·
                  exact fin15Anchored_clause27459 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27460 chi hbad
                ·
                  exact fin15Anchored_clause27461 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27462 chi hbad
                ·
                  exact fin15Anchored_clause27463 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27464 chi hbad
                ·
                  exact fin15Anchored_clause27465 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27466 chi hbad
                ·
                  exact fin15Anchored_clause27467 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27468 chi hbad
                ·
                  exact fin15Anchored_clause27469 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27470 chi hbad
                ·
                  exact fin15Anchored_clause27471 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27472 chi hbad
                ·
                  exact fin15Anchored_clause27473 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27474 chi hbad
                ·
                  exact fin15Anchored_clause27475 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27476 chi hbad
                ·
                  exact fin15Anchored_clause27477 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27478 chi hbad
                ·
                  exact fin15Anchored_clause27479 chi hbad
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
                  exact fin15Anchored_clause27480 chi hbad
                ·
                  exact fin15Anchored_clause27481 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27482 chi hbad
                ·
                  exact fin15Anchored_clause27483 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27484 chi hbad
                ·
                  exact fin15Anchored_clause27485 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27486 chi hbad
                ·
                  exact fin15Anchored_clause27487 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27488 chi hbad
                ·
                  exact fin15Anchored_clause27489 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27490 chi hbad
                ·
                  exact fin15Anchored_clause27491 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27492 chi hbad
                ·
                  exact fin15Anchored_clause27493 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27494 chi hbad
                ·
                  exact fin15Anchored_clause27495 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27496 chi hbad
                ·
                  exact fin15Anchored_clause27497 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27498 chi hbad
                ·
                  exact fin15Anchored_clause27499 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27500 chi hbad
                ·
                  exact fin15Anchored_clause27501 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27502 chi hbad
                ·
                  exact fin15Anchored_clause27503 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27504 chi hbad
                ·
                  exact fin15Anchored_clause27505 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27506 chi hbad
                ·
                  exact fin15Anchored_clause27507 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27508 chi hbad
                ·
                  exact fin15Anchored_clause27509 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27510 chi hbad
                ·
                  exact fin15Anchored_clause27511 chi hbad

end ErdosSzekeres

end
