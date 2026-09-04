module

public import ErdosSzekeres.Fin15AnchoredClauseChunk214
public import ErdosSzekeres.Fin15AnchoredClauseChunk215
public import ErdosSzekeres.Fin15AnchoredClauseChunk216

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 109. -/

theorem fin15Anchored_rejectSemanticSegment109
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom4623 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1638 chi ∧
      Fin15AnchoredAtom1690 chi ∧
      Fin15AnchoredAtom1746 chi) ∨
      ((Fin15AnchoredAtom4624 chi ∧
      ¬Fin15AnchoredAtom1634 chi) ∨
      (Fin15AnchoredAtom4624 chi ∧
      ¬Fin15AnchoredAtom1636 chi))) ∨
      (((Fin15AnchoredAtom4624 chi ∧
      ¬Fin15AnchoredAtom1691 chi) ∨
      (¬Fin15AnchoredAtom4624 chi ∧
      Fin15AnchoredAtom1633 chi ∧
      Fin15AnchoredAtom1634 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1691 chi ∧
      Fin15AnchoredAtom1747 chi)) ∨
      ((Fin15AnchoredAtom4625 chi ∧
      ¬Fin15AnchoredAtom1692 chi) ∨
      (Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom1636 chi)))) ∨
      ((((Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom1637 chi) ∨
      (Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom1638 chi)) ∨
      ((Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom1694 chi) ∨
      (Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom1750 chi))) ∨
      (((¬Fin15AnchoredAtom4627 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1637 chi ∧
      Fin15AnchoredAtom1638 chi ∧
      Fin15AnchoredAtom1694 chi ∧
      Fin15AnchoredAtom1750 chi) ∨
      (Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom1639 chi)) ∨
      ((Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom1640 chi) ∨
      (Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom1645 chi))))) ∨
      (((((Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom1660 chi) ∨
      (Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom1751 chi)) ∨
      ((¬Fin15AnchoredAtom4628 chi ∧
      Fin15AnchoredAtom1639 chi ∧
      Fin15AnchoredAtom1640 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1660 chi ∧
      Fin15AnchoredAtom1751 chi) ∨
      (Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom1639 chi))) ∨
      (((Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom1642 chi) ∨
      (Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom1647 chi)) ∨
      ((Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom1662 chi) ∨
      (Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom1753 chi)))) ∨
      ((((¬Fin15AnchoredAtom4630 chi ∧
      Fin15AnchoredAtom1639 chi ∧
      Fin15AnchoredAtom1642 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1662 chi ∧
      Fin15AnchoredAtom1753 chi) ∨
      (Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom1643 chi)) ∨
      ((Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom1648 chi) ∨
      (Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom1663 chi))) ∨
      (((Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom1754 chi) ∨
      (¬Fin15AnchoredAtom4631 chi ∧
      Fin15AnchoredAtom1639 chi ∧
      Fin15AnchoredAtom1643 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1663 chi ∧
      Fin15AnchoredAtom1754 chi)) ∨
      ((Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom1639 chi) ∨
      (Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom1644 chi)))))) ∨
      ((((((Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom1649 chi) ∨
      (Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom1664 chi)) ∨
      ((Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom1755 chi) ∨
      (¬Fin15AnchoredAtom4632 chi ∧
      Fin15AnchoredAtom1639 chi ∧
      Fin15AnchoredAtom1644 chi ∧
      Fin15AnchoredAtom1649 chi ∧
      Fin15AnchoredAtom1664 chi ∧
      Fin15AnchoredAtom1755 chi))) ∨
      (((Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom1640 chi) ∨
      (Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom1642 chi)) ∨
      ((Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom1651 chi) ∨
      (Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom1666 chi)))) ∨
      ((((Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom1757 chi) ∨
      (¬Fin15AnchoredAtom4634 chi ∧
      Fin15AnchoredAtom1640 chi ∧
      Fin15AnchoredAtom1642 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1666 chi ∧
      Fin15AnchoredAtom1757 chi)) ∨
      ((Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom1640 chi) ∨
      (Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom1643 chi))) ∨
      (((Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom1652 chi) ∨
      (Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom1667 chi)) ∨
      ((Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom1758 chi) ∨
      (¬Fin15AnchoredAtom4635 chi ∧
      Fin15AnchoredAtom1640 chi ∧
      Fin15AnchoredAtom1643 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1667 chi ∧
      Fin15AnchoredAtom1758 chi))))) ∨
      (((((Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom1640 chi) ∨
      (Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom1644 chi)) ∨
      ((Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom1653 chi) ∨
      (Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom1668 chi))) ∨
      (((Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom1759 chi) ∨
      (Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom1642 chi)) ∨
      ((Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom1643 chi) ∨
      (Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom1657 chi)))) ∨
      ((((Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom1672 chi) ∨
      (Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom1763 chi)) ∨
      ((¬Fin15AnchoredAtom4640 chi ∧
      Fin15AnchoredAtom1642 chi ∧
      Fin15AnchoredAtom1643 chi ∧
      Fin15AnchoredAtom1657 chi ∧
      Fin15AnchoredAtom1672 chi ∧
      Fin15AnchoredAtom1763 chi) ∨
      (Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom1642 chi))) ∨
      (((Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom1644 chi) ∨
      (Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom1658 chi)) ∨
      ((Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom1673 chi) ∨
      (Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom1764 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom4641 chi ∧
      Fin15AnchoredAtom1642 chi ∧
      Fin15AnchoredAtom1644 chi ∧
      Fin15AnchoredAtom1658 chi ∧
      Fin15AnchoredAtom1673 chi ∧
      Fin15AnchoredAtom1764 chi) ∨
      ((Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom1643 chi) ∨
      (Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom1644 chi))) ∨
      (((Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom1659 chi) ∨
      (Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom1674 chi)) ∨
      ((Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom1765 chi) ∨
      (¬Fin15AnchoredAtom4642 chi ∧
      Fin15AnchoredAtom1643 chi ∧
      Fin15AnchoredAtom1644 chi ∧
      Fin15AnchoredAtom1659 chi ∧
      Fin15AnchoredAtom1674 chi ∧
      Fin15AnchoredAtom1765 chi)))) ∨
      ((((Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom1645 chi) ∨
      (Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom1650 chi)) ∨
      ((Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom1675 chi) ∨
      (Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom1766 chi))) ∨
      (((¬Fin15AnchoredAtom4643 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1646 chi ∧
      Fin15AnchoredAtom1650 chi ∧
      Fin15AnchoredAtom1675 chi ∧
      Fin15AnchoredAtom1766 chi) ∨
      (Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom1645 chi)) ∨
      ((Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom1647 chi) ∨
      (Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom1651 chi))))) ∨
      (((((Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom1676 chi) ∨
      (Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom1767 chi)) ∨
      ((¬Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1767 chi) ∨
      (Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom1645 chi))) ∨
      (((Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom1648 chi) ∨
      (Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom1652 chi)) ∨
      ((Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom1677 chi) ∨
      (Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom1768 chi)))) ∨
      ((((¬Fin15AnchoredAtom4645 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1677 chi ∧
      Fin15AnchoredAtom1768 chi) ∨
      (Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom1645 chi)) ∨
      ((Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom1649 chi) ∨
      (Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom1653 chi))) ∨
      (((Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom1678 chi) ∨
      (Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom1769 chi)) ∨
      ((¬Fin15AnchoredAtom4646 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1649 chi ∧
      Fin15AnchoredAtom1653 chi ∧
      Fin15AnchoredAtom1678 chi ∧
      Fin15AnchoredAtom1769 chi) ∨
      (Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom1647 chi)))))) ∨
      ((((((Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom1679 chi) ∨
      (Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom1770 chi)) ∨
      ((¬Fin15AnchoredAtom4647 chi ∧
      Fin15AnchoredAtom1646 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1654 chi ∧
      Fin15AnchoredAtom1679 chi ∧
      Fin15AnchoredAtom1770 chi) ∨
      (Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom1646 chi))) ∨
      (((Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom1648 chi) ∨
      (Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom1680 chi)) ∨
      ((Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom1771 chi) ∨
      (¬Fin15AnchoredAtom4648 chi ∧
      Fin15AnchoredAtom1646 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1655 chi ∧
      Fin15AnchoredAtom1680 chi ∧
      Fin15AnchoredAtom1771 chi)))) ∨
      ((((Fin15AnchoredAtom4649 chi ∧
      ¬Fin15AnchoredAtom1649 chi) ∨
      (Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom1647 chi)) ∨
      ((Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom1648 chi) ∨
      (Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom1657 chi))) ∨
      (((Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom1682 chi) ∨
      (Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom1773 chi)) ∨
      ((¬Fin15AnchoredAtom4650 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1657 chi ∧
      Fin15AnchoredAtom1682 chi ∧
      Fin15AnchoredAtom1773 chi) ∨
      (Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom1647 chi))))) ∨
      (((((Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom1649 chi) ∨
      (Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom1658 chi)) ∨
      ((Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom1683 chi) ∨
      (Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom1774 chi))) ∨
      (((¬Fin15AnchoredAtom4651 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1649 chi ∧
      Fin15AnchoredAtom1658 chi ∧
      Fin15AnchoredAtom1683 chi ∧
      Fin15AnchoredAtom1774 chi) ∨
      (Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom1648 chi)) ∨
      ((Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom1649 chi) ∨
      (Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom1659 chi)))) ∨
      ((((Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom1684 chi) ∨
      (Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom1775 chi)) ∨
      ((¬Fin15AnchoredAtom4652 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1649 chi ∧
      Fin15AnchoredAtom1659 chi ∧
      Fin15AnchoredAtom1684 chi ∧
      Fin15AnchoredAtom1775 chi) ∨
      (Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom1650 chi))) ∨
      (((Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom1651 chi) ∨
      (Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom1685 chi)) ∨
      ((Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom1776 chi) ∨
      (¬Fin15AnchoredAtom4653 chi ∧
      Fin15AnchoredAtom1650 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1654 chi ∧
      Fin15AnchoredAtom1685 chi ∧
      Fin15AnchoredAtom1776 chi)))))))) ∨
      (((((((Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom1650 chi) ∨
      ((Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom1652 chi) ∨
      (Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom1686 chi))) ∨
      (((¬Fin15AnchoredAtom4654 chi ∧
      Fin15AnchoredAtom1650 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1655 chi ∧
      Fin15AnchoredAtom1686 chi ∧
      Fin15AnchoredAtom1777 chi) ∨
      (Fin15AnchoredAtom4655 chi ∧
      ¬Fin15AnchoredAtom1650 chi)) ∨
      ((Fin15AnchoredAtom4655 chi ∧
      ¬Fin15AnchoredAtom1653 chi) ∨
      (Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom1651 chi)))) ∨
      ((((Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom1652 chi) ∨
      (Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom1657 chi)) ∨
      ((Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom1779 chi))) ∨
      (((¬Fin15AnchoredAtom4656 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1657 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1779 chi) ∨
      (Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom1651 chi)) ∨
      ((Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom1653 chi) ∨
      (Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom1658 chi))))) ∨
      (((((Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom1689 chi) ∨
      (Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom1780 chi)) ∨
      ((¬Fin15AnchoredAtom4657 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1653 chi ∧
      Fin15AnchoredAtom1658 chi ∧
      Fin15AnchoredAtom1689 chi ∧
      Fin15AnchoredAtom1780 chi) ∨
      (Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom1652 chi))) ∨
      (((Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom1653 chi) ∨
      (Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom1659 chi)) ∨
      ((Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom1690 chi) ∨
      (Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom1781 chi)))) ∨
      ((((¬Fin15AnchoredAtom4658 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1653 chi ∧
      Fin15AnchoredAtom1659 chi ∧
      Fin15AnchoredAtom1690 chi ∧
      Fin15AnchoredAtom1781 chi) ∨
      (Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom1654 chi)) ∨
      ((Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom1655 chi) ∨
      (Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom1657 chi))) ∨
      (((Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom1691 chi) ∨
      (Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom1782 chi)) ∨
      ((Fin15AnchoredAtom4660 chi ∧
      ¬Fin15AnchoredAtom1658 chi) ∨
      (Fin15AnchoredAtom4660 chi ∧
      ¬Fin15AnchoredAtom1692 chi)))))) ∨
      ((((((Fin15AnchoredAtom4660 chi ∧
      ¬Fin15AnchoredAtom1783 chi) ∨
      (Fin15AnchoredAtom4661 chi ∧
      ¬Fin15AnchoredAtom1656 chi)) ∨
      ((Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom1657 chi) ∨
      (Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom1658 chi))) ∨
      (((Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom1659 chi) ∨
      (Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom1694 chi)) ∨
      ((Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom1785 chi) ∨
      (¬Fin15AnchoredAtom4662 chi ∧
      Fin15AnchoredAtom1657 chi ∧
      Fin15AnchoredAtom1658 chi ∧
      Fin15AnchoredAtom1659 chi ∧
      Fin15AnchoredAtom1694 chi ∧
      Fin15AnchoredAtom1785 chi)))) ∨
      ((((Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom1660 chi) ∨
      (Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom1662 chi)) ∨
      ((Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom1666 chi) ∨
      (Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom1676 chi))) ∨
      (((Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom1787 chi) ∨
      (¬Fin15AnchoredAtom4664 chi ∧
      Fin15AnchoredAtom1660 chi ∧
      Fin15AnchoredAtom1662 chi ∧
      Fin15AnchoredAtom1666 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1787 chi)) ∨
      ((Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom1660 chi) ∨
      (Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom1663 chi))))) ∨
      (((((Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom1667 chi) ∨
      (Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom1677 chi)) ∨
      ((Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom1788 chi) ∨
      (¬Fin15AnchoredAtom4665 chi ∧
      Fin15AnchoredAtom1660 chi ∧
      Fin15AnchoredAtom1663 chi ∧
      Fin15AnchoredAtom1667 chi ∧
      Fin15AnchoredAtom1677 chi ∧
      Fin15AnchoredAtom1788 chi))) ∨
      (((Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom1660 chi) ∨
      (Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom1664 chi)) ∨
      ((Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom1668 chi) ∨
      (Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom1678 chi)))) ∨
      ((((Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom1789 chi) ∨
      (¬Fin15AnchoredAtom4666 chi ∧
      Fin15AnchoredAtom1660 chi ∧
      Fin15AnchoredAtom1664 chi ∧
      Fin15AnchoredAtom1668 chi ∧
      Fin15AnchoredAtom1678 chi ∧
      Fin15AnchoredAtom1789 chi)) ∨
      ((Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom1662 chi) ∨
      (Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom1663 chi))) ∨
      (((Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom1672 chi) ∨
      (Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom1682 chi)) ∨
      ((Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom1793 chi) ∨
      (¬Fin15AnchoredAtom4670 chi ∧
      Fin15AnchoredAtom1662 chi ∧
      Fin15AnchoredAtom1663 chi ∧
      Fin15AnchoredAtom1672 chi ∧
      Fin15AnchoredAtom1682 chi ∧
      Fin15AnchoredAtom1793 chi))))))) ∨
      (((((((Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom1662 chi) ∨
      (Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom1664 chi)) ∨
      ((Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom1673 chi) ∨
      (Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom1683 chi))) ∨
      (((Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom1794 chi) ∨
      (¬Fin15AnchoredAtom4671 chi ∧
      Fin15AnchoredAtom1662 chi ∧
      Fin15AnchoredAtom1664 chi ∧
      Fin15AnchoredAtom1673 chi ∧
      Fin15AnchoredAtom1683 chi ∧
      Fin15AnchoredAtom1794 chi)) ∨
      ((Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom1663 chi) ∨
      (Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom1664 chi)))) ∨
      ((((Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom1674 chi) ∨
      (Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom1684 chi)) ∨
      ((Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom1795 chi) ∨
      (¬Fin15AnchoredAtom4672 chi ∧
      Fin15AnchoredAtom1663 chi ∧
      Fin15AnchoredAtom1664 chi ∧
      Fin15AnchoredAtom1674 chi ∧
      Fin15AnchoredAtom1684 chi ∧
      Fin15AnchoredAtom1795 chi))) ∨
      (((Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom1666 chi) ∨
      (Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom1667 chi)) ∨
      ((Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom1672 chi) ∨
      (Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom1688 chi))))) ∨
      (((((Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom1799 chi) ∨
      (¬Fin15AnchoredAtom4676 chi ∧
      Fin15AnchoredAtom1666 chi ∧
      Fin15AnchoredAtom1667 chi ∧
      Fin15AnchoredAtom1672 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1799 chi)) ∨
      ((Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom1666 chi) ∨
      (Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom1668 chi))) ∨
      (((Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom1673 chi) ∨
      (Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom1689 chi)) ∨
      ((Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom1800 chi) ∨
      (¬Fin15AnchoredAtom4677 chi ∧
      Fin15AnchoredAtom1666 chi ∧
      Fin15AnchoredAtom1668 chi ∧
      Fin15AnchoredAtom1673 chi ∧
      Fin15AnchoredAtom1689 chi ∧
      Fin15AnchoredAtom1800 chi)))) ∨
      ((((Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom1667 chi) ∨
      (Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom1668 chi)) ∨
      ((Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom1674 chi) ∨
      (Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom1690 chi))) ∨
      (((Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom1801 chi) ∨
      (¬Fin15AnchoredAtom4678 chi ∧
      Fin15AnchoredAtom1667 chi ∧
      Fin15AnchoredAtom1668 chi ∧
      Fin15AnchoredAtom1674 chi ∧
      Fin15AnchoredAtom1690 chi ∧
      Fin15AnchoredAtom1801 chi)) ∨
      ((Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom1672 chi) ∨
      (Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom1673 chi)))))) ∨
      ((((((Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom1674 chi) ∨
      (Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom1694 chi)) ∨
      ((Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom1805 chi) ∨
      (¬Fin15AnchoredAtom4682 chi ∧
      Fin15AnchoredAtom1672 chi ∧
      Fin15AnchoredAtom1673 chi ∧
      Fin15AnchoredAtom1674 chi ∧
      Fin15AnchoredAtom1694 chi ∧
      Fin15AnchoredAtom1805 chi))) ∨
      (((Fin15AnchoredAtom4683 chi ∧
      ¬Fin15AnchoredAtom1675 chi) ∨
      (Fin15AnchoredAtom4683 chi ∧
      ¬Fin15AnchoredAtom1679 chi)) ∨
      ((Fin15AnchoredAtom4683 chi ∧
      ¬Fin15AnchoredAtom1806 chi) ∨
      (¬Fin15AnchoredAtom4683 chi ∧
      Fin15AnchoredAtom1675 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1679 chi ∧
      Fin15AnchoredAtom1685 chi ∧
      Fin15AnchoredAtom1806 chi)))) ∨
      ((((Fin15AnchoredAtom4684 chi ∧
      ¬Fin15AnchoredAtom1675 chi) ∨
      (Fin15AnchoredAtom4684 chi ∧
      ¬Fin15AnchoredAtom1677 chi)) ∨
      ((Fin15AnchoredAtom4685 chi ∧
      ¬Fin15AnchoredAtom1675 chi) ∨
      (Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom1676 chi))) ∨
      (((Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom1677 chi) ∨
      (Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom1682 chi)) ∨
      ((Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom1809 chi))))) ∨
      (((((¬Fin15AnchoredAtom4686 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1677 chi ∧
      Fin15AnchoredAtom1682 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1809 chi) ∨
      (Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom1676 chi)) ∨
      ((Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom1678 chi) ∨
      (Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom1683 chi))) ∨
      (((Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom1689 chi) ∨
      (Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom1810 chi)) ∨
      ((¬Fin15AnchoredAtom4687 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1678 chi ∧
      Fin15AnchoredAtom1683 chi ∧
      Fin15AnchoredAtom1689 chi ∧
      Fin15AnchoredAtom1810 chi) ∨
      (Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom1677 chi)))) ∨
      ((((Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom1678 chi) ∨
      (Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom1684 chi)) ∨
      ((Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom1690 chi) ∨
      (Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom1811 chi))) ∨
      (((¬Fin15AnchoredAtom4688 chi ∧
      Fin15AnchoredAtom1677 chi ∧
      Fin15AnchoredAtom1678 chi ∧
      Fin15AnchoredAtom1684 chi ∧
      Fin15AnchoredAtom1690 chi ∧
      Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom4689 chi ∧
      ¬Fin15AnchoredAtom1682 chi)) ∨
      ((Fin15AnchoredAtom4690 chi ∧
      ¬Fin15AnchoredAtom1683 chi) ∨
      (Fin15AnchoredAtom4690 chi ∧
      ¬Fin15AnchoredAtom1813 chi)))))))))) := by
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
                exact fin15Anchored_clause27512 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27513 chi hbad
                ·
                  exact fin15Anchored_clause27514 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27515 chi hbad
                ·
                  exact fin15Anchored_clause27516 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27517 chi hbad
                ·
                  exact fin15Anchored_clause27518 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27519 chi hbad
                ·
                  exact fin15Anchored_clause27520 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27521 chi hbad
                ·
                  exact fin15Anchored_clause27522 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27523 chi hbad
                ·
                  exact fin15Anchored_clause27524 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27525 chi hbad
                ·
                  exact fin15Anchored_clause27526 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27527 chi hbad
                ·
                  exact fin15Anchored_clause27528 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27529 chi hbad
                ·
                  exact fin15Anchored_clause27530 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27531 chi hbad
                ·
                  exact fin15Anchored_clause27532 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27533 chi hbad
                ·
                  exact fin15Anchored_clause27534 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27535 chi hbad
                ·
                  exact fin15Anchored_clause27536 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27537 chi hbad
                ·
                  exact fin15Anchored_clause27538 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27539 chi hbad
                ·
                  exact fin15Anchored_clause27540 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27541 chi hbad
                ·
                  exact fin15Anchored_clause27542 chi hbad
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
                  exact fin15Anchored_clause27543 chi hbad
                ·
                  exact fin15Anchored_clause27544 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27545 chi hbad
                ·
                  exact fin15Anchored_clause27546 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27547 chi hbad
                ·
                  exact fin15Anchored_clause27548 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27549 chi hbad
                ·
                  exact fin15Anchored_clause27550 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27551 chi hbad
                ·
                  exact fin15Anchored_clause27552 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27553 chi hbad
                ·
                  exact fin15Anchored_clause27554 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27555 chi hbad
                ·
                  exact fin15Anchored_clause27556 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27557 chi hbad
                ·
                  exact fin15Anchored_clause27558 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27559 chi hbad
                ·
                  exact fin15Anchored_clause27560 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27561 chi hbad
                ·
                  exact fin15Anchored_clause27562 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27563 chi hbad
                ·
                  exact fin15Anchored_clause27564 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27565 chi hbad
                ·
                  exact fin15Anchored_clause27566 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27567 chi hbad
                ·
                  exact fin15Anchored_clause27568 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27569 chi hbad
                ·
                  exact fin15Anchored_clause27570 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27571 chi hbad
                ·
                  exact fin15Anchored_clause27572 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27573 chi hbad
                ·
                  exact fin15Anchored_clause27574 chi hbad
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
                exact fin15Anchored_clause27575 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27576 chi hbad
                ·
                  exact fin15Anchored_clause27577 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27578 chi hbad
                ·
                  exact fin15Anchored_clause27579 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27580 chi hbad
                ·
                  exact fin15Anchored_clause27581 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27582 chi hbad
                ·
                  exact fin15Anchored_clause27583 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27584 chi hbad
                ·
                  exact fin15Anchored_clause27585 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27586 chi hbad
                ·
                  exact fin15Anchored_clause27587 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27588 chi hbad
                ·
                  exact fin15Anchored_clause27589 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27590 chi hbad
                ·
                  exact fin15Anchored_clause27591 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27592 chi hbad
                ·
                  exact fin15Anchored_clause27593 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27594 chi hbad
                ·
                  exact fin15Anchored_clause27595 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27596 chi hbad
                ·
                  exact fin15Anchored_clause27597 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27598 chi hbad
                ·
                  exact fin15Anchored_clause27599 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27600 chi hbad
                ·
                  exact fin15Anchored_clause27601 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27602 chi hbad
                ·
                  exact fin15Anchored_clause27603 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27604 chi hbad
                ·
                  exact fin15Anchored_clause27605 chi hbad
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
                  exact fin15Anchored_clause27606 chi hbad
                ·
                  exact fin15Anchored_clause27607 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27608 chi hbad
                ·
                  exact fin15Anchored_clause27609 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27610 chi hbad
                ·
                  exact fin15Anchored_clause27611 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27612 chi hbad
                ·
                  exact fin15Anchored_clause27613 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27614 chi hbad
                ·
                  exact fin15Anchored_clause27615 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27616 chi hbad
                ·
                  exact fin15Anchored_clause27617 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27618 chi hbad
                ·
                  exact fin15Anchored_clause27619 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27620 chi hbad
                ·
                  exact fin15Anchored_clause27621 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27622 chi hbad
                ·
                  exact fin15Anchored_clause27623 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27624 chi hbad
                ·
                  exact fin15Anchored_clause27625 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27626 chi hbad
                ·
                  exact fin15Anchored_clause27627 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27628 chi hbad
                ·
                  exact fin15Anchored_clause27629 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27630 chi hbad
                ·
                  exact fin15Anchored_clause27631 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27632 chi hbad
                ·
                  exact fin15Anchored_clause27633 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27634 chi hbad
                ·
                  exact fin15Anchored_clause27635 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27636 chi hbad
                ·
                  exact fin15Anchored_clause27637 chi hbad
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
                exact fin15Anchored_clause27638 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27639 chi hbad
                ·
                  exact fin15Anchored_clause27640 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27641 chi hbad
                ·
                  exact fin15Anchored_clause27642 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27643 chi hbad
                ·
                  exact fin15Anchored_clause27644 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27645 chi hbad
                ·
                  exact fin15Anchored_clause27646 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27647 chi hbad
                ·
                  exact fin15Anchored_clause27648 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27649 chi hbad
                ·
                  exact fin15Anchored_clause27650 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27651 chi hbad
                ·
                  exact fin15Anchored_clause27652 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27653 chi hbad
                ·
                  exact fin15Anchored_clause27654 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27655 chi hbad
                ·
                  exact fin15Anchored_clause27656 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27657 chi hbad
                ·
                  exact fin15Anchored_clause27658 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27659 chi hbad
                ·
                  exact fin15Anchored_clause27660 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27661 chi hbad
                ·
                  exact fin15Anchored_clause27662 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27663 chi hbad
                ·
                  exact fin15Anchored_clause27664 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27665 chi hbad
                ·
                  exact fin15Anchored_clause27666 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27667 chi hbad
                ·
                  exact fin15Anchored_clause27668 chi hbad
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
                  exact fin15Anchored_clause27669 chi hbad
                ·
                  exact fin15Anchored_clause27670 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27671 chi hbad
                ·
                  exact fin15Anchored_clause27672 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27673 chi hbad
                ·
                  exact fin15Anchored_clause27674 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27675 chi hbad
                ·
                  exact fin15Anchored_clause27676 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27677 chi hbad
                ·
                  exact fin15Anchored_clause27678 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27679 chi hbad
                ·
                  exact fin15Anchored_clause27680 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27681 chi hbad
                ·
                  exact fin15Anchored_clause27682 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27683 chi hbad
                ·
                  exact fin15Anchored_clause27684 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27685 chi hbad
                ·
                  exact fin15Anchored_clause27686 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27687 chi hbad
                ·
                  exact fin15Anchored_clause27688 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27689 chi hbad
                ·
                  exact fin15Anchored_clause27690 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27691 chi hbad
                ·
                  exact fin15Anchored_clause27692 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27693 chi hbad
                ·
                  exact fin15Anchored_clause27694 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27695 chi hbad
                ·
                  exact fin15Anchored_clause27696 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27697 chi hbad
                ·
                  exact fin15Anchored_clause27698 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27699 chi hbad
                ·
                  exact fin15Anchored_clause27700 chi hbad
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
                  exact fin15Anchored_clause27701 chi hbad
                ·
                  exact fin15Anchored_clause27702 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27703 chi hbad
                ·
                  exact fin15Anchored_clause27704 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27705 chi hbad
                ·
                  exact fin15Anchored_clause27706 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27707 chi hbad
                ·
                  exact fin15Anchored_clause27708 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27709 chi hbad
                ·
                  exact fin15Anchored_clause27710 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27711 chi hbad
                ·
                  exact fin15Anchored_clause27712 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27713 chi hbad
                ·
                  exact fin15Anchored_clause27714 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27715 chi hbad
                ·
                  exact fin15Anchored_clause27716 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27717 chi hbad
                ·
                  exact fin15Anchored_clause27718 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27719 chi hbad
                ·
                  exact fin15Anchored_clause27720 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27721 chi hbad
                ·
                  exact fin15Anchored_clause27722 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27723 chi hbad
                ·
                  exact fin15Anchored_clause27724 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27725 chi hbad
                ·
                  exact fin15Anchored_clause27726 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27727 chi hbad
                ·
                  exact fin15Anchored_clause27728 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27729 chi hbad
                ·
                  exact fin15Anchored_clause27730 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27731 chi hbad
                ·
                  exact fin15Anchored_clause27732 chi hbad
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
                  exact fin15Anchored_clause27733 chi hbad
                ·
                  exact fin15Anchored_clause27734 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27735 chi hbad
                ·
                  exact fin15Anchored_clause27736 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27737 chi hbad
                ·
                  exact fin15Anchored_clause27738 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27739 chi hbad
                ·
                  exact fin15Anchored_clause27740 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27741 chi hbad
                ·
                  exact fin15Anchored_clause27742 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27743 chi hbad
                ·
                  exact fin15Anchored_clause27744 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27745 chi hbad
                ·
                  exact fin15Anchored_clause27746 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27747 chi hbad
                ·
                  exact fin15Anchored_clause27748 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27749 chi hbad
                ·
                  exact fin15Anchored_clause27750 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27751 chi hbad
                ·
                  exact fin15Anchored_clause27752 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27753 chi hbad
                ·
                  exact fin15Anchored_clause27754 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27755 chi hbad
                ·
                  exact fin15Anchored_clause27756 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27757 chi hbad
                ·
                  exact fin15Anchored_clause27758 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27759 chi hbad
                ·
                  exact fin15Anchored_clause27760 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27761 chi hbad
                ·
                  exact fin15Anchored_clause27762 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27763 chi hbad
                ·
                  exact fin15Anchored_clause27764 chi hbad

end ErdosSzekeres

end
