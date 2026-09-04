module

public import ErdosSzekeres.Fin15AnchoredClauseChunk216
public import ErdosSzekeres.Fin15AnchoredClauseChunk217
public import ErdosSzekeres.Fin15AnchoredClauseChunk218

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 110. -/

theorem fin15Anchored_rejectSemanticSegment110
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom4691 chi ∧
      ¬Fin15AnchoredAtom1681 chi) ∨
      ((Fin15AnchoredAtom4691 chi ∧
      ¬Fin15AnchoredAtom1814 chi) ∨
      (Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom1682 chi))) ∨
      (((Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom1683 chi) ∨
      (Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom1684 chi)) ∨
      ((Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom1694 chi) ∨
      (Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom1815 chi)))) ∨
      ((((¬Fin15AnchoredAtom4692 chi ∧
      Fin15AnchoredAtom1682 chi ∧
      Fin15AnchoredAtom1683 chi ∧
      Fin15AnchoredAtom1684 chi ∧
      Fin15AnchoredAtom1694 chi ∧
      Fin15AnchoredAtom1815 chi) ∨
      (Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom1686 chi)) ∨
      ((Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom1691 chi))) ∨
      (((Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom1816 chi) ∨
      (¬Fin15AnchoredAtom4693 chi ∧
      Fin15AnchoredAtom1685 chi ∧
      Fin15AnchoredAtom1686 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1691 chi ∧
      Fin15AnchoredAtom1816 chi)) ∨
      ((Fin15AnchoredAtom4694 chi ∧
      ¬Fin15AnchoredAtom1685 chi) ∨
      (Fin15AnchoredAtom4694 chi ∧
      ¬Fin15AnchoredAtom1689 chi))))) ∨
      (((((Fin15AnchoredAtom4695 chi ∧
      ¬Fin15AnchoredAtom1818 chi) ∨
      (Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom1688 chi)) ∨
      ((Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom1689 chi) ∨
      (Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom1690 chi))) ∨
      (((Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom1694 chi) ∨
      (Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom1819 chi)) ∨
      ((¬Fin15AnchoredAtom4696 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1689 chi ∧
      Fin15AnchoredAtom1690 chi ∧
      Fin15AnchoredAtom1694 chi ∧
      Fin15AnchoredAtom1819 chi) ∨
      (Fin15AnchoredAtom4697 chi ∧
      ¬Fin15AnchoredAtom1692 chi)))) ∨
      ((((Fin15AnchoredAtom4697 chi ∧
      ¬Fin15AnchoredAtom1820 chi) ∨
      (Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom1695 chi)) ∨
      ((Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom1696 chi) ∨
      (Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom1701 chi))) ∨
      (((Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom1716 chi) ∨
      (Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom1751 chi)) ∨
      ((¬Fin15AnchoredAtom4698 chi ∧
      Fin15AnchoredAtom1695 chi ∧
      Fin15AnchoredAtom1696 chi ∧
      Fin15AnchoredAtom1701 chi ∧
      Fin15AnchoredAtom1716 chi ∧
      Fin15AnchoredAtom1751 chi) ∨
      (Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom1695 chi)))))) ∨
      ((((((Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom1703 chi)) ∨
      ((Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom1718 chi) ∨
      (Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom1753 chi))) ∨
      (((¬Fin15AnchoredAtom4700 chi ∧
      Fin15AnchoredAtom1695 chi ∧
      Fin15AnchoredAtom1698 chi ∧
      Fin15AnchoredAtom1703 chi ∧
      Fin15AnchoredAtom1718 chi ∧
      Fin15AnchoredAtom1753 chi) ∨
      (Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom1695 chi)) ∨
      ((Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom1699 chi) ∨
      (Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom1704 chi)))) ∨
      ((((Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom1719 chi) ∨
      (Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom1754 chi)) ∨
      ((¬Fin15AnchoredAtom4701 chi ∧
      Fin15AnchoredAtom1695 chi ∧
      Fin15AnchoredAtom1699 chi ∧
      Fin15AnchoredAtom1704 chi ∧
      Fin15AnchoredAtom1719 chi ∧
      Fin15AnchoredAtom1754 chi) ∨
      (Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom1695 chi))) ∨
      (((Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom1700 chi) ∨
      (Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom1705 chi)) ∨
      ((Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom1720 chi) ∨
      (Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom1755 chi))))) ∨
      (((((¬Fin15AnchoredAtom4702 chi ∧
      Fin15AnchoredAtom1695 chi ∧
      Fin15AnchoredAtom1700 chi ∧
      Fin15AnchoredAtom1705 chi ∧
      Fin15AnchoredAtom1720 chi ∧
      Fin15AnchoredAtom1755 chi) ∨
      (Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom1696 chi)) ∨
      ((Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom1707 chi))) ∨
      (((Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom1722 chi) ∨
      (Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom1757 chi)) ∨
      ((¬Fin15AnchoredAtom4704 chi ∧
      Fin15AnchoredAtom1696 chi ∧
      Fin15AnchoredAtom1698 chi ∧
      Fin15AnchoredAtom1707 chi ∧
      Fin15AnchoredAtom1722 chi ∧
      Fin15AnchoredAtom1757 chi) ∨
      (Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom1696 chi)))) ∨
      ((((Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom1699 chi) ∨
      (Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom1708 chi)) ∨
      ((Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom1723 chi) ∨
      (Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom1758 chi))) ∨
      (((¬Fin15AnchoredAtom4705 chi ∧
      Fin15AnchoredAtom1696 chi ∧
      Fin15AnchoredAtom1699 chi ∧
      Fin15AnchoredAtom1708 chi ∧
      Fin15AnchoredAtom1723 chi ∧
      Fin15AnchoredAtom1758 chi) ∨
      (Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom1696 chi)) ∨
      ((Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom1700 chi) ∨
      (Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom1709 chi))))))) ∨
      ((((((Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom1724 chi) ∨
      ((Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom1759 chi) ∨
      (¬Fin15AnchoredAtom4706 chi ∧
      Fin15AnchoredAtom1696 chi ∧
      Fin15AnchoredAtom1700 chi ∧
      Fin15AnchoredAtom1709 chi ∧
      Fin15AnchoredAtom1724 chi ∧
      Fin15AnchoredAtom1759 chi))) ∨
      (((Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom1699 chi)) ∨
      ((Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom1713 chi) ∨
      (Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom1728 chi)))) ∨
      ((((Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom1763 chi) ∨
      (¬Fin15AnchoredAtom4710 chi ∧
      Fin15AnchoredAtom1698 chi ∧
      Fin15AnchoredAtom1699 chi ∧
      Fin15AnchoredAtom1713 chi ∧
      Fin15AnchoredAtom1728 chi ∧
      Fin15AnchoredAtom1763 chi)) ∨
      ((Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom1700 chi))) ∨
      (((Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom1714 chi) ∨
      (Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom1729 chi)) ∨
      ((Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom1764 chi) ∨
      (¬Fin15AnchoredAtom4711 chi ∧
      Fin15AnchoredAtom1698 chi ∧
      Fin15AnchoredAtom1700 chi ∧
      Fin15AnchoredAtom1714 chi ∧
      Fin15AnchoredAtom1729 chi ∧
      Fin15AnchoredAtom1764 chi))))) ∨
      (((((Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom1699 chi) ∨
      (Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom1700 chi)) ∨
      ((Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom1715 chi) ∨
      (Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom1730 chi))) ∨
      (((Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom1765 chi) ∨
      (¬Fin15AnchoredAtom4712 chi ∧
      Fin15AnchoredAtom1699 chi ∧
      Fin15AnchoredAtom1700 chi ∧
      Fin15AnchoredAtom1715 chi ∧
      Fin15AnchoredAtom1730 chi ∧
      Fin15AnchoredAtom1765 chi)) ∨
      ((Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom1701 chi) ∨
      (Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom1702 chi)))) ∨
      ((((Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom1731 chi) ∨
      (Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom1766 chi)) ∨
      ((¬Fin15AnchoredAtom4713 chi ∧
      Fin15AnchoredAtom1701 chi ∧
      Fin15AnchoredAtom1702 chi ∧
      Fin15AnchoredAtom1706 chi ∧
      Fin15AnchoredAtom1731 chi ∧
      Fin15AnchoredAtom1766 chi) ∨
      (Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom1701 chi))) ∨
      (((Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom1703 chi) ∨
      (Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom1707 chi)) ∨
      ((Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      (Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom1767 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom4714 chi ∧
      Fin15AnchoredAtom1701 chi ∧
      Fin15AnchoredAtom1703 chi ∧
      Fin15AnchoredAtom1707 chi ∧
      Fin15AnchoredAtom1732 chi ∧
      Fin15AnchoredAtom1767 chi) ∨
      (Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom1701 chi)) ∨
      ((Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom1704 chi) ∨
      (Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom1708 chi))) ∨
      (((Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom1733 chi) ∨
      (Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom1768 chi)) ∨
      ((¬Fin15AnchoredAtom4715 chi ∧
      Fin15AnchoredAtom1701 chi ∧
      Fin15AnchoredAtom1704 chi ∧
      Fin15AnchoredAtom1708 chi ∧
      Fin15AnchoredAtom1733 chi ∧
      Fin15AnchoredAtom1768 chi) ∨
      (Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom1701 chi)))) ∨
      ((((Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom1705 chi) ∨
      (Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom1709 chi)) ∨
      ((Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom1734 chi) ∨
      (Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom1769 chi))) ∨
      (((¬Fin15AnchoredAtom4716 chi ∧
      Fin15AnchoredAtom1701 chi ∧
      Fin15AnchoredAtom1705 chi ∧
      Fin15AnchoredAtom1709 chi ∧
      Fin15AnchoredAtom1734 chi ∧
      Fin15AnchoredAtom1769 chi) ∨
      (Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom1703 chi)) ∨
      ((Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom1710 chi) ∨
      (Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom1735 chi))))) ∨
      (((((Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom1770 chi) ∨
      (¬Fin15AnchoredAtom4717 chi ∧
      Fin15AnchoredAtom1702 chi ∧
      Fin15AnchoredAtom1703 chi ∧
      Fin15AnchoredAtom1710 chi ∧
      Fin15AnchoredAtom1735 chi ∧
      Fin15AnchoredAtom1770 chi)) ∨
      ((Fin15AnchoredAtom4718 chi ∧
      ¬Fin15AnchoredAtom1704 chi) ∨
      (Fin15AnchoredAtom4718 chi ∧
      ¬Fin15AnchoredAtom1736 chi))) ∨
      (((Fin15AnchoredAtom4719 chi ∧
      ¬Fin15AnchoredAtom1705 chi) ∨
      (Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom1703 chi)) ∨
      ((Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom1704 chi) ∨
      (Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom1713 chi)))) ∨
      ((((Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom1738 chi) ∨
      (Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom1773 chi)) ∨
      ((¬Fin15AnchoredAtom4720 chi ∧
      Fin15AnchoredAtom1703 chi ∧
      Fin15AnchoredAtom1704 chi ∧
      Fin15AnchoredAtom1713 chi ∧
      Fin15AnchoredAtom1738 chi ∧
      Fin15AnchoredAtom1773 chi) ∨
      (Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom1703 chi))) ∨
      (((Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom1705 chi) ∨
      (Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom1714 chi)) ∨
      ((Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom1739 chi) ∨
      (Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom1774 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom4721 chi ∧
      Fin15AnchoredAtom1703 chi ∧
      Fin15AnchoredAtom1705 chi ∧
      Fin15AnchoredAtom1714 chi ∧
      Fin15AnchoredAtom1739 chi ∧
      Fin15AnchoredAtom1774 chi) ∨
      ((Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom1704 chi) ∨
      (Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom1705 chi))) ∨
      (((Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom1715 chi) ∨
      (Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom1740 chi)) ∨
      ((Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom1775 chi) ∨
      (¬Fin15AnchoredAtom4722 chi ∧
      Fin15AnchoredAtom1704 chi ∧
      Fin15AnchoredAtom1705 chi ∧
      Fin15AnchoredAtom1715 chi ∧
      Fin15AnchoredAtom1740 chi ∧
      Fin15AnchoredAtom1775 chi)))) ∨
      ((((Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom1706 chi) ∨
      (Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom1707 chi)) ∨
      ((Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom1741 chi) ∨
      (Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom1776 chi))) ∨
      (((¬Fin15AnchoredAtom4723 chi ∧
      Fin15AnchoredAtom1706 chi ∧
      Fin15AnchoredAtom1707 chi ∧
      Fin15AnchoredAtom1710 chi ∧
      Fin15AnchoredAtom1741 chi ∧
      Fin15AnchoredAtom1776 chi) ∨
      (Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom1706 chi)) ∨
      ((Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom1708 chi) ∨
      (Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom1711 chi))))) ∨
      (((((Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom1742 chi) ∨
      (Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom1777 chi)) ∨
      ((Fin15AnchoredAtom4725 chi ∧
      ¬Fin15AnchoredAtom1709 chi) ∨
      (Fin15AnchoredAtom4725 chi ∧
      ¬Fin15AnchoredAtom1743 chi))) ∨
      (((Fin15AnchoredAtom4725 chi ∧
      ¬Fin15AnchoredAtom1778 chi) ∨
      (Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom1707 chi)) ∨
      ((Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom1708 chi) ∨
      (Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom1713 chi)))) ∨
      ((((Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom1744 chi) ∨
      (Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom1779 chi)) ∨
      ((¬Fin15AnchoredAtom4726 chi ∧
      Fin15AnchoredAtom1707 chi ∧
      Fin15AnchoredAtom1708 chi ∧
      Fin15AnchoredAtom1713 chi ∧
      Fin15AnchoredAtom1744 chi ∧
      Fin15AnchoredAtom1779 chi) ∨
      (Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom1707 chi))) ∨
      (((Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom1709 chi) ∨
      (Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom1714 chi)) ∨
      ((Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom1745 chi) ∨
      (Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom1780 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom4727 chi ∧
      Fin15AnchoredAtom1707 chi ∧
      Fin15AnchoredAtom1709 chi ∧
      Fin15AnchoredAtom1714 chi ∧
      Fin15AnchoredAtom1745 chi ∧
      Fin15AnchoredAtom1780 chi) ∨
      (Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom1708 chi)) ∨
      ((Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom1709 chi) ∨
      (Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom1715 chi))) ∨
      (((Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom1746 chi) ∨
      (Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom1781 chi)) ∨
      ((¬Fin15AnchoredAtom4728 chi ∧
      Fin15AnchoredAtom1708 chi ∧
      Fin15AnchoredAtom1709 chi ∧
      Fin15AnchoredAtom1715 chi ∧
      Fin15AnchoredAtom1746 chi ∧
      Fin15AnchoredAtom1781 chi) ∨
      (Fin15AnchoredAtom4729 chi ∧
      ¬Fin15AnchoredAtom1713 chi)))) ∨
      ((((Fin15AnchoredAtom4729 chi ∧
      ¬Fin15AnchoredAtom1782 chi) ∨
      (Fin15AnchoredAtom4730 chi ∧
      ¬Fin15AnchoredAtom1714 chi)) ∨
      ((Fin15AnchoredAtom4730 chi ∧
      ¬Fin15AnchoredAtom1783 chi) ∨
      (Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom1713 chi))) ∨
      (((Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom1714 chi) ∨
      (Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom1715 chi)) ∨
      ((Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom1750 chi) ∨
      (Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom1785 chi))))) ∨
      (((((¬Fin15AnchoredAtom4732 chi ∧
      Fin15AnchoredAtom1713 chi ∧
      Fin15AnchoredAtom1714 chi ∧
      Fin15AnchoredAtom1715 chi ∧
      Fin15AnchoredAtom1750 chi ∧
      Fin15AnchoredAtom1785 chi) ∨
      (Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom1716 chi)) ∨
      ((Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom1718 chi) ∨
      (Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom1722 chi))) ∨
      (((Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      (Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom1787 chi)) ∨
      ((¬Fin15AnchoredAtom4734 chi ∧
      Fin15AnchoredAtom1716 chi ∧
      Fin15AnchoredAtom1718 chi ∧
      Fin15AnchoredAtom1722 chi ∧
      Fin15AnchoredAtom1732 chi ∧
      Fin15AnchoredAtom1787 chi) ∨
      (Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom1716 chi)))) ∨
      ((((Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom1719 chi) ∨
      (Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom1723 chi)) ∨
      ((Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom1733 chi) ∨
      (Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom1788 chi))) ∨
      (((¬Fin15AnchoredAtom4735 chi ∧
      Fin15AnchoredAtom1716 chi ∧
      Fin15AnchoredAtom1719 chi ∧
      Fin15AnchoredAtom1723 chi ∧
      Fin15AnchoredAtom1733 chi ∧
      Fin15AnchoredAtom1788 chi) ∨
      (Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom1716 chi)) ∨
      ((Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom1720 chi) ∨
      (Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom1724 chi))))))) ∨
      ((((((Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom1734 chi) ∨
      ((Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom1789 chi) ∨
      (¬Fin15AnchoredAtom4736 chi ∧
      Fin15AnchoredAtom1716 chi ∧
      Fin15AnchoredAtom1720 chi ∧
      Fin15AnchoredAtom1724 chi ∧
      Fin15AnchoredAtom1734 chi ∧
      Fin15AnchoredAtom1789 chi))) ∨
      (((Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom1718 chi) ∨
      (Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom1719 chi)) ∨
      ((Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom1728 chi) ∨
      (Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom1738 chi)))) ∨
      ((((Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom1793 chi) ∨
      (¬Fin15AnchoredAtom4740 chi ∧
      Fin15AnchoredAtom1718 chi ∧
      Fin15AnchoredAtom1719 chi ∧
      Fin15AnchoredAtom1728 chi ∧
      Fin15AnchoredAtom1738 chi ∧
      Fin15AnchoredAtom1793 chi)) ∨
      ((Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom1718 chi) ∨
      (Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom1720 chi))) ∨
      (((Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom1729 chi) ∨
      (Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom1739 chi)) ∨
      ((Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom1794 chi) ∨
      (¬Fin15AnchoredAtom4741 chi ∧
      Fin15AnchoredAtom1718 chi ∧
      Fin15AnchoredAtom1720 chi ∧
      Fin15AnchoredAtom1729 chi ∧
      Fin15AnchoredAtom1739 chi ∧
      Fin15AnchoredAtom1794 chi))))) ∨
      (((((Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom1719 chi) ∨
      (Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom1720 chi)) ∨
      ((Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom1730 chi) ∨
      (Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom1740 chi))) ∨
      (((Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom1795 chi) ∨
      (¬Fin15AnchoredAtom4742 chi ∧
      Fin15AnchoredAtom1719 chi ∧
      Fin15AnchoredAtom1720 chi ∧
      Fin15AnchoredAtom1730 chi ∧
      Fin15AnchoredAtom1740 chi ∧
      Fin15AnchoredAtom1795 chi)) ∨
      ((Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom1722 chi) ∨
      (Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom1723 chi)))) ∨
      ((((Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom1728 chi) ∨
      (Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom1744 chi)) ∨
      ((Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom1799 chi) ∨
      (¬Fin15AnchoredAtom4746 chi ∧
      Fin15AnchoredAtom1722 chi ∧
      Fin15AnchoredAtom1723 chi ∧
      Fin15AnchoredAtom1728 chi ∧
      Fin15AnchoredAtom1744 chi ∧
      Fin15AnchoredAtom1799 chi))) ∨
      (((Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom1722 chi) ∨
      (Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom1724 chi)) ∨
      ((Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom1745 chi) ∨
      (Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom1800 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom4747 chi ∧
      Fin15AnchoredAtom1722 chi ∧
      Fin15AnchoredAtom1724 chi ∧
      Fin15AnchoredAtom1729 chi ∧
      Fin15AnchoredAtom1745 chi ∧
      Fin15AnchoredAtom1800 chi) ∨
      (Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom1723 chi)) ∨
      ((Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom1724 chi) ∨
      (Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom1730 chi))) ∨
      (((Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom1746 chi) ∨
      (Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom1801 chi)) ∨
      ((¬Fin15AnchoredAtom4748 chi ∧
      Fin15AnchoredAtom1723 chi ∧
      Fin15AnchoredAtom1724 chi ∧
      Fin15AnchoredAtom1730 chi ∧
      Fin15AnchoredAtom1746 chi ∧
      Fin15AnchoredAtom1801 chi) ∨
      (Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom1728 chi)))) ∨
      ((((Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom1729 chi) ∨
      (Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom1730 chi)) ∨
      ((Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom1750 chi) ∨
      (Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom1805 chi))) ∨
      (((¬Fin15AnchoredAtom4752 chi ∧
      Fin15AnchoredAtom1728 chi ∧
      Fin15AnchoredAtom1729 chi ∧
      Fin15AnchoredAtom1730 chi ∧
      Fin15AnchoredAtom1750 chi ∧
      Fin15AnchoredAtom1805 chi) ∨
      (Fin15AnchoredAtom4753 chi ∧
      ¬Fin15AnchoredAtom1732 chi)) ∨
      ((Fin15AnchoredAtom4753 chi ∧
      ¬Fin15AnchoredAtom1735 chi) ∨
      (Fin15AnchoredAtom4753 chi ∧
      ¬Fin15AnchoredAtom1806 chi))))) ∨
      (((((¬Fin15AnchoredAtom4753 chi ∧
      Fin15AnchoredAtom1731 chi ∧
      Fin15AnchoredAtom1732 chi ∧
      Fin15AnchoredAtom1735 chi ∧
      Fin15AnchoredAtom1741 chi ∧
      Fin15AnchoredAtom1806 chi) ∨
      (Fin15AnchoredAtom4754 chi ∧
      ¬Fin15AnchoredAtom1733 chi)) ∨
      ((Fin15AnchoredAtom4754 chi ∧
      ¬Fin15AnchoredAtom1736 chi) ∨
      (Fin15AnchoredAtom4755 chi ∧
      ¬Fin15AnchoredAtom1731 chi))) ∨
      (((Fin15AnchoredAtom4755 chi ∧
      ¬Fin15AnchoredAtom1734 chi) ∨
      (Fin15AnchoredAtom4755 chi ∧
      ¬Fin15AnchoredAtom1808 chi)) ∨
      ((Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      (Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom1733 chi)))) ∨
      ((((Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom1738 chi) ∨
      (Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom1744 chi)) ∨
      ((Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom1809 chi) ∨
      (¬Fin15AnchoredAtom4756 chi ∧
      Fin15AnchoredAtom1732 chi ∧
      Fin15AnchoredAtom1733 chi ∧
      Fin15AnchoredAtom1738 chi ∧
      Fin15AnchoredAtom1744 chi ∧
      Fin15AnchoredAtom1809 chi))) ∨
      (((Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      (Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom1734 chi)) ∨
      ((Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom1739 chi) ∨
      (Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom1745 chi)))))))))) := by
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
                exact fin15Anchored_clause27765 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27766 chi hbad
                ·
                  exact fin15Anchored_clause27767 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27768 chi hbad
                ·
                  exact fin15Anchored_clause27769 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27770 chi hbad
                ·
                  exact fin15Anchored_clause27771 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27772 chi hbad
                ·
                  exact fin15Anchored_clause27773 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27774 chi hbad
                ·
                  exact fin15Anchored_clause27775 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27776 chi hbad
                ·
                  exact fin15Anchored_clause27777 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27778 chi hbad
                ·
                  exact fin15Anchored_clause27779 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27780 chi hbad
                ·
                  exact fin15Anchored_clause27781 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27782 chi hbad
                ·
                  exact fin15Anchored_clause27783 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27784 chi hbad
                ·
                  exact fin15Anchored_clause27785 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27786 chi hbad
                ·
                  exact fin15Anchored_clause27787 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27788 chi hbad
                ·
                  exact fin15Anchored_clause27789 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27790 chi hbad
                ·
                  exact fin15Anchored_clause27791 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27792 chi hbad
                ·
                  exact fin15Anchored_clause27793 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27794 chi hbad
                ·
                  exact fin15Anchored_clause27795 chi hbad
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
                  exact fin15Anchored_clause27796 chi hbad
                ·
                  exact fin15Anchored_clause27797 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27798 chi hbad
                ·
                  exact fin15Anchored_clause27799 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27800 chi hbad
                ·
                  exact fin15Anchored_clause27801 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27802 chi hbad
                ·
                  exact fin15Anchored_clause27803 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27804 chi hbad
                ·
                  exact fin15Anchored_clause27805 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27806 chi hbad
                ·
                  exact fin15Anchored_clause27807 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27808 chi hbad
                ·
                  exact fin15Anchored_clause27809 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27810 chi hbad
                ·
                  exact fin15Anchored_clause27811 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27812 chi hbad
                ·
                  exact fin15Anchored_clause27813 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27814 chi hbad
                ·
                  exact fin15Anchored_clause27815 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27816 chi hbad
                ·
                  exact fin15Anchored_clause27817 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27818 chi hbad
                ·
                  exact fin15Anchored_clause27819 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27820 chi hbad
                ·
                  exact fin15Anchored_clause27821 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27822 chi hbad
                ·
                  exact fin15Anchored_clause27823 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27824 chi hbad
                ·
                  exact fin15Anchored_clause27825 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27826 chi hbad
                ·
                  exact fin15Anchored_clause27827 chi hbad
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
                exact fin15Anchored_clause27828 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27829 chi hbad
                ·
                  exact fin15Anchored_clause27830 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27831 chi hbad
                ·
                  exact fin15Anchored_clause27832 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27833 chi hbad
                ·
                  exact fin15Anchored_clause27834 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27835 chi hbad
                ·
                  exact fin15Anchored_clause27836 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27837 chi hbad
                ·
                  exact fin15Anchored_clause27838 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27839 chi hbad
                ·
                  exact fin15Anchored_clause27840 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27841 chi hbad
                ·
                  exact fin15Anchored_clause27842 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27843 chi hbad
                ·
                  exact fin15Anchored_clause27844 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27845 chi hbad
                ·
                  exact fin15Anchored_clause27846 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27847 chi hbad
                ·
                  exact fin15Anchored_clause27848 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27849 chi hbad
                ·
                  exact fin15Anchored_clause27850 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27851 chi hbad
                ·
                  exact fin15Anchored_clause27852 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27853 chi hbad
                ·
                  exact fin15Anchored_clause27854 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27855 chi hbad
                ·
                  exact fin15Anchored_clause27856 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27857 chi hbad
                ·
                  exact fin15Anchored_clause27858 chi hbad
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
                  exact fin15Anchored_clause27859 chi hbad
                ·
                  exact fin15Anchored_clause27860 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27861 chi hbad
                ·
                  exact fin15Anchored_clause27862 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27863 chi hbad
                ·
                  exact fin15Anchored_clause27864 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27865 chi hbad
                ·
                  exact fin15Anchored_clause27866 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27867 chi hbad
                ·
                  exact fin15Anchored_clause27868 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27869 chi hbad
                ·
                  exact fin15Anchored_clause27870 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27871 chi hbad
                ·
                  exact fin15Anchored_clause27872 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27873 chi hbad
                ·
                  exact fin15Anchored_clause27874 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27875 chi hbad
                ·
                  exact fin15Anchored_clause27876 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27877 chi hbad
                ·
                  exact fin15Anchored_clause27878 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27879 chi hbad
                ·
                  exact fin15Anchored_clause27880 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27881 chi hbad
                ·
                  exact fin15Anchored_clause27882 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27883 chi hbad
                ·
                  exact fin15Anchored_clause27884 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27885 chi hbad
                ·
                  exact fin15Anchored_clause27886 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27887 chi hbad
                ·
                  exact fin15Anchored_clause27888 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27889 chi hbad
                ·
                  exact fin15Anchored_clause27890 chi hbad
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
                exact fin15Anchored_clause27891 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27892 chi hbad
                ·
                  exact fin15Anchored_clause27893 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27894 chi hbad
                ·
                  exact fin15Anchored_clause27895 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27896 chi hbad
                ·
                  exact fin15Anchored_clause27897 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27898 chi hbad
                ·
                  exact fin15Anchored_clause27899 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27900 chi hbad
                ·
                  exact fin15Anchored_clause27901 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27902 chi hbad
                ·
                  exact fin15Anchored_clause27903 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27904 chi hbad
                ·
                  exact fin15Anchored_clause27905 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27906 chi hbad
                ·
                  exact fin15Anchored_clause27907 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27908 chi hbad
                ·
                  exact fin15Anchored_clause27909 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27910 chi hbad
                ·
                  exact fin15Anchored_clause27911 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27912 chi hbad
                ·
                  exact fin15Anchored_clause27913 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27914 chi hbad
                ·
                  exact fin15Anchored_clause27915 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27916 chi hbad
                ·
                  exact fin15Anchored_clause27917 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27918 chi hbad
                ·
                  exact fin15Anchored_clause27919 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27920 chi hbad
                ·
                  exact fin15Anchored_clause27921 chi hbad
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
                  exact fin15Anchored_clause27922 chi hbad
                ·
                  exact fin15Anchored_clause27923 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27924 chi hbad
                ·
                  exact fin15Anchored_clause27925 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27926 chi hbad
                ·
                  exact fin15Anchored_clause27927 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27928 chi hbad
                ·
                  exact fin15Anchored_clause27929 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27930 chi hbad
                ·
                  exact fin15Anchored_clause27931 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27932 chi hbad
                ·
                  exact fin15Anchored_clause27933 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27934 chi hbad
                ·
                  exact fin15Anchored_clause27935 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27936 chi hbad
                ·
                  exact fin15Anchored_clause27937 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27938 chi hbad
                ·
                  exact fin15Anchored_clause27939 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27940 chi hbad
                ·
                  exact fin15Anchored_clause27941 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27942 chi hbad
                ·
                  exact fin15Anchored_clause27943 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27944 chi hbad
                ·
                  exact fin15Anchored_clause27945 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27946 chi hbad
                ·
                  exact fin15Anchored_clause27947 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27948 chi hbad
                ·
                  exact fin15Anchored_clause27949 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27950 chi hbad
                ·
                  exact fin15Anchored_clause27951 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27952 chi hbad
                ·
                  exact fin15Anchored_clause27953 chi hbad
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
                exact fin15Anchored_clause27954 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27955 chi hbad
                ·
                  exact fin15Anchored_clause27956 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27957 chi hbad
                ·
                  exact fin15Anchored_clause27958 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27959 chi hbad
                ·
                  exact fin15Anchored_clause27960 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27961 chi hbad
                ·
                  exact fin15Anchored_clause27962 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27963 chi hbad
                ·
                  exact fin15Anchored_clause27964 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27965 chi hbad
                ·
                  exact fin15Anchored_clause27966 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27967 chi hbad
                ·
                  exact fin15Anchored_clause27968 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27969 chi hbad
                ·
                  exact fin15Anchored_clause27970 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27971 chi hbad
                ·
                  exact fin15Anchored_clause27972 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27973 chi hbad
                ·
                  exact fin15Anchored_clause27974 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27975 chi hbad
                ·
                  exact fin15Anchored_clause27976 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27977 chi hbad
                ·
                  exact fin15Anchored_clause27978 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27979 chi hbad
                ·
                  exact fin15Anchored_clause27980 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27981 chi hbad
                ·
                  exact fin15Anchored_clause27982 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27983 chi hbad
                ·
                  exact fin15Anchored_clause27984 chi hbad
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
                  exact fin15Anchored_clause27985 chi hbad
                ·
                  exact fin15Anchored_clause27986 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27987 chi hbad
                ·
                  exact fin15Anchored_clause27988 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27989 chi hbad
                ·
                  exact fin15Anchored_clause27990 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27991 chi hbad
                ·
                  exact fin15Anchored_clause27992 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27993 chi hbad
                ·
                  exact fin15Anchored_clause27994 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27995 chi hbad
                ·
                  exact fin15Anchored_clause27996 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27997 chi hbad
                ·
                  exact fin15Anchored_clause27998 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause27999 chi hbad
                ·
                  exact fin15Anchored_clause28000 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28001 chi hbad
                ·
                  exact fin15Anchored_clause28002 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28003 chi hbad
                ·
                  exact fin15Anchored_clause28004 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28005 chi hbad
                ·
                  exact fin15Anchored_clause28006 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28007 chi hbad
                ·
                  exact fin15Anchored_clause28008 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28009 chi hbad
                ·
                  exact fin15Anchored_clause28010 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28011 chi hbad
                ·
                  exact fin15Anchored_clause28012 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28013 chi hbad
                ·
                  exact fin15Anchored_clause28014 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28015 chi hbad
                ·
                  exact fin15Anchored_clause28016 chi hbad

end ErdosSzekeres

end
