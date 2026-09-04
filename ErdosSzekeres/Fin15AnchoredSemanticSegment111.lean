module

public import ErdosSzekeres.Fin15AnchoredClauseChunk218
public import ErdosSzekeres.Fin15AnchoredClauseChunk219
public import ErdosSzekeres.Fin15AnchoredClauseChunk220

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 111. -/

theorem fin15Anchored_rejectSemanticSegment111
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom1810 chi) ∨
      ((¬Fin15AnchoredAtom4757 chi ∧
      Fin15AnchoredAtom1732 chi ∧
      Fin15AnchoredAtom1734 chi ∧
      Fin15AnchoredAtom1739 chi ∧
      Fin15AnchoredAtom1745 chi ∧
      Fin15AnchoredAtom1810 chi) ∨
      (Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom1733 chi))) ∨
      (((Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom1734 chi) ∨
      (Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom1740 chi)) ∨
      ((Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom1746 chi) ∨
      (Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom1811 chi)))) ∨
      ((((¬Fin15AnchoredAtom4758 chi ∧
      Fin15AnchoredAtom1733 chi ∧
      Fin15AnchoredAtom1734 chi ∧
      Fin15AnchoredAtom1740 chi ∧
      Fin15AnchoredAtom1746 chi ∧
      Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom4759 chi ∧
      ¬Fin15AnchoredAtom1735 chi)) ∨
      ((Fin15AnchoredAtom4759 chi ∧
      ¬Fin15AnchoredAtom1736 chi) ∨
      (Fin15AnchoredAtom4759 chi ∧
      ¬Fin15AnchoredAtom1738 chi))) ∨
      (((¬Fin15AnchoredAtom4759 chi ∧
      Fin15AnchoredAtom1735 chi ∧
      Fin15AnchoredAtom1736 chi ∧
      Fin15AnchoredAtom1738 chi ∧
      Fin15AnchoredAtom1747 chi ∧
      Fin15AnchoredAtom1812 chi) ∨
      (Fin15AnchoredAtom4760 chi ∧
      ¬Fin15AnchoredAtom1735 chi)) ∨
      ((Fin15AnchoredAtom4760 chi ∧
      ¬Fin15AnchoredAtom1739 chi) ∨
      (Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom1738 chi))))) ∨
      (((((Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom1739 chi) ∨
      (Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom1740 chi)) ∨
      ((Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom1750 chi) ∨
      (Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom1815 chi))) ∨
      (((¬Fin15AnchoredAtom4762 chi ∧
      Fin15AnchoredAtom1738 chi ∧
      Fin15AnchoredAtom1739 chi ∧
      Fin15AnchoredAtom1740 chi ∧
      Fin15AnchoredAtom1750 chi ∧
      Fin15AnchoredAtom1815 chi) ∨
      (Fin15AnchoredAtom4763 chi ∧
      ¬Fin15AnchoredAtom1742 chi)) ∨
      ((Fin15AnchoredAtom4763 chi ∧
      ¬Fin15AnchoredAtom1744 chi) ∨
      (Fin15AnchoredAtom4763 chi ∧
      ¬Fin15AnchoredAtom1747 chi)))) ∨
      ((((Fin15AnchoredAtom4763 chi ∧
      ¬Fin15AnchoredAtom1816 chi) ∨
      (¬Fin15AnchoredAtom4763 chi ∧
      Fin15AnchoredAtom1741 chi ∧
      Fin15AnchoredAtom1742 chi ∧
      Fin15AnchoredAtom1744 chi ∧
      Fin15AnchoredAtom1747 chi ∧
      Fin15AnchoredAtom1816 chi)) ∨
      ((Fin15AnchoredAtom4764 chi ∧
      ¬Fin15AnchoredAtom1743 chi) ∨
      (Fin15AnchoredAtom4764 chi ∧
      ¬Fin15AnchoredAtom1745 chi))) ∨
      (((Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom1744 chi) ∨
      (Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom1745 chi)) ∨
      ((Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom1746 chi) ∨
      (Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom1750 chi)))))) ∨
      ((((((Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom1819 chi) ∨
      (¬Fin15AnchoredAtom4766 chi ∧
      Fin15AnchoredAtom1744 chi ∧
      Fin15AnchoredAtom1745 chi ∧
      Fin15AnchoredAtom1746 chi ∧
      Fin15AnchoredAtom1750 chi ∧
      Fin15AnchoredAtom1819 chi)) ∨
      ((Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom1751 chi) ∨
      (Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom1753 chi))) ∨
      (((Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom1757 chi) ∨
      (Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom1767 chi)) ∨
      ((Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom1787 chi) ∨
      (¬Fin15AnchoredAtom4769 chi ∧
      Fin15AnchoredAtom1751 chi ∧
      Fin15AnchoredAtom1753 chi ∧
      Fin15AnchoredAtom1757 chi ∧
      Fin15AnchoredAtom1767 chi ∧
      Fin15AnchoredAtom1787 chi)))) ∨
      ((((Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom1751 chi) ∨
      (Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom1754 chi)) ∨
      ((Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom1758 chi) ∨
      (Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom1768 chi))) ∨
      (((Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom1788 chi) ∨
      (¬Fin15AnchoredAtom4770 chi ∧
      Fin15AnchoredAtom1751 chi ∧
      Fin15AnchoredAtom1754 chi ∧
      Fin15AnchoredAtom1758 chi ∧
      Fin15AnchoredAtom1768 chi ∧
      Fin15AnchoredAtom1788 chi)) ∨
      ((Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom1751 chi) ∨
      (Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom1755 chi))))) ∨
      (((((Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom1759 chi) ∨
      (Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom1769 chi)) ∨
      ((Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom1789 chi) ∨
      (¬Fin15AnchoredAtom4771 chi ∧
      Fin15AnchoredAtom1751 chi ∧
      Fin15AnchoredAtom1755 chi ∧
      Fin15AnchoredAtom1759 chi ∧
      Fin15AnchoredAtom1769 chi ∧
      Fin15AnchoredAtom1789 chi))) ∨
      (((Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom1753 chi) ∨
      (Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom1754 chi)) ∨
      ((Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom1763 chi) ∨
      (Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom1773 chi)))) ∨
      ((((Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom1793 chi) ∨
      (¬Fin15AnchoredAtom4775 chi ∧
      Fin15AnchoredAtom1753 chi ∧
      Fin15AnchoredAtom1754 chi ∧
      Fin15AnchoredAtom1763 chi ∧
      Fin15AnchoredAtom1773 chi ∧
      Fin15AnchoredAtom1793 chi)) ∨
      ((Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom1753 chi) ∨
      (Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom1755 chi))) ∨
      (((Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom1764 chi) ∨
      (Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom1774 chi)) ∨
      ((Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom1794 chi) ∨
      (¬Fin15AnchoredAtom4776 chi ∧
      Fin15AnchoredAtom1753 chi ∧
      Fin15AnchoredAtom1755 chi ∧
      Fin15AnchoredAtom1764 chi ∧
      Fin15AnchoredAtom1774 chi ∧
      Fin15AnchoredAtom1794 chi))))))) ∨
      ((((((Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom1754 chi) ∨
      ((Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom1755 chi) ∨
      (Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom1765 chi))) ∨
      (((Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom1775 chi) ∨
      (Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom1795 chi)) ∨
      ((¬Fin15AnchoredAtom4777 chi ∧
      Fin15AnchoredAtom1754 chi ∧
      Fin15AnchoredAtom1755 chi ∧
      Fin15AnchoredAtom1765 chi ∧
      Fin15AnchoredAtom1775 chi ∧
      Fin15AnchoredAtom1795 chi) ∨
      (Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom1757 chi)))) ∨
      ((((Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom1758 chi) ∨
      (Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom1763 chi)) ∨
      ((Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom1779 chi) ∨
      (Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom1799 chi))) ∨
      (((¬Fin15AnchoredAtom4781 chi ∧
      Fin15AnchoredAtom1757 chi ∧
      Fin15AnchoredAtom1758 chi ∧
      Fin15AnchoredAtom1763 chi ∧
      Fin15AnchoredAtom1779 chi ∧
      Fin15AnchoredAtom1799 chi) ∨
      (Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom1757 chi)) ∨
      ((Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom1759 chi) ∨
      (Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom1780 chi))))) ∨
      (((((Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom1800 chi) ∨
      (¬Fin15AnchoredAtom4782 chi ∧
      Fin15AnchoredAtom1757 chi ∧
      Fin15AnchoredAtom1759 chi ∧
      Fin15AnchoredAtom1764 chi ∧
      Fin15AnchoredAtom1780 chi ∧
      Fin15AnchoredAtom1800 chi)) ∨
      ((Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom1758 chi) ∨
      (Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom1759 chi))) ∨
      (((Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom1781 chi) ∨
      (Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom1801 chi)) ∨
      ((¬Fin15AnchoredAtom4783 chi ∧
      Fin15AnchoredAtom1758 chi ∧
      Fin15AnchoredAtom1759 chi ∧
      Fin15AnchoredAtom1765 chi ∧
      Fin15AnchoredAtom1781 chi ∧
      Fin15AnchoredAtom1801 chi) ∨
      (Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom1763 chi)))) ∨
      ((((Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom1764 chi) ∨
      (Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom1765 chi)) ∨
      ((Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom1785 chi) ∨
      (Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom1805 chi))) ∨
      (((¬Fin15AnchoredAtom4787 chi ∧
      Fin15AnchoredAtom1763 chi ∧
      Fin15AnchoredAtom1764 chi ∧
      Fin15AnchoredAtom1765 chi ∧
      Fin15AnchoredAtom1785 chi ∧
      Fin15AnchoredAtom1805 chi) ∨
      (Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom1766 chi)) ∨
      ((Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom1767 chi) ∨
      (Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom1770 chi)))))) ∨
      ((((((Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom1776 chi) ∨
      (Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom1806 chi)) ∨
      ((¬Fin15AnchoredAtom4788 chi ∧
      Fin15AnchoredAtom1766 chi ∧
      Fin15AnchoredAtom1767 chi ∧
      Fin15AnchoredAtom1770 chi ∧
      Fin15AnchoredAtom1776 chi ∧
      Fin15AnchoredAtom1806 chi) ∨
      (Fin15AnchoredAtom4789 chi ∧
      ¬Fin15AnchoredAtom1766 chi))) ∨
      (((Fin15AnchoredAtom4789 chi ∧
      ¬Fin15AnchoredAtom1807 chi) ∨
      (¬Fin15AnchoredAtom4789 chi ∧
      Fin15AnchoredAtom1766 chi ∧
      Fin15AnchoredAtom1768 chi ∧
      Fin15AnchoredAtom1771 chi ∧
      Fin15AnchoredAtom1777 chi ∧
      Fin15AnchoredAtom1807 chi)) ∨
      ((Fin15AnchoredAtom4790 chi ∧
      ¬Fin15AnchoredAtom1769 chi) ∨
      (Fin15AnchoredAtom4790 chi ∧
      ¬Fin15AnchoredAtom1778 chi)))) ∨
      ((((¬Fin15AnchoredAtom4790 chi ∧
      Fin15AnchoredAtom1766 chi ∧
      Fin15AnchoredAtom1769 chi ∧
      Fin15AnchoredAtom1772 chi ∧
      Fin15AnchoredAtom1778 chi ∧
      Fin15AnchoredAtom1808 chi) ∨
      (Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom1767 chi)) ∨
      ((Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom1768 chi) ∨
      (Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom1773 chi))) ∨
      (((Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom1779 chi) ∨
      (Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom1809 chi)) ∨
      ((¬Fin15AnchoredAtom4791 chi ∧
      Fin15AnchoredAtom1767 chi ∧
      Fin15AnchoredAtom1768 chi ∧
      Fin15AnchoredAtom1773 chi ∧
      Fin15AnchoredAtom1779 chi ∧
      Fin15AnchoredAtom1809 chi) ∨
      (Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom1767 chi))))) ∨
      (((((Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom1769 chi) ∨
      (Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom1774 chi)) ∨
      ((Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom1780 chi) ∨
      (Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom1810 chi))) ∨
      (((¬Fin15AnchoredAtom4792 chi ∧
      Fin15AnchoredAtom1767 chi ∧
      Fin15AnchoredAtom1769 chi ∧
      Fin15AnchoredAtom1774 chi ∧
      Fin15AnchoredAtom1780 chi ∧
      Fin15AnchoredAtom1810 chi) ∨
      (Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom1768 chi)) ∨
      ((Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom1769 chi) ∨
      (Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom1775 chi)))) ∨
      ((((Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom1781 chi) ∨
      (Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom1811 chi)) ∨
      ((¬Fin15AnchoredAtom4793 chi ∧
      Fin15AnchoredAtom1768 chi ∧
      Fin15AnchoredAtom1769 chi ∧
      Fin15AnchoredAtom1775 chi ∧
      Fin15AnchoredAtom1781 chi ∧
      Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom4794 chi ∧
      ¬Fin15AnchoredAtom1770 chi))) ∨
      (((Fin15AnchoredAtom4794 chi ∧
      ¬Fin15AnchoredAtom1773 chi) ∨
      (Fin15AnchoredAtom4794 chi ∧
      ¬Fin15AnchoredAtom1812 chi)) ∨
      ((Fin15AnchoredAtom4795 chi ∧
      ¬Fin15AnchoredAtom1774 chi) ∨
      (Fin15AnchoredAtom4795 chi ∧
      ¬Fin15AnchoredAtom1783 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom4795 chi ∧
      Fin15AnchoredAtom1770 chi ∧
      Fin15AnchoredAtom1772 chi ∧
      Fin15AnchoredAtom1774 chi ∧
      Fin15AnchoredAtom1783 chi ∧
      Fin15AnchoredAtom1813 chi) ∨
      ((Fin15AnchoredAtom4796 chi ∧
      ¬Fin15AnchoredAtom1772 chi) ∨
      (¬Fin15AnchoredAtom4796 chi ∧
      Fin15AnchoredAtom1771 chi ∧
      Fin15AnchoredAtom1772 chi ∧
      Fin15AnchoredAtom1775 chi ∧
      Fin15AnchoredAtom1784 chi ∧
      Fin15AnchoredAtom1814 chi))) ∨
      (((Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom1773 chi) ∨
      (Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom1774 chi)) ∨
      ((Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom1775 chi) ∨
      (Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom1785 chi)))) ∨
      ((((Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom1815 chi) ∨
      (¬Fin15AnchoredAtom4797 chi ∧
      Fin15AnchoredAtom1773 chi ∧
      Fin15AnchoredAtom1774 chi ∧
      Fin15AnchoredAtom1775 chi ∧
      Fin15AnchoredAtom1785 chi ∧
      Fin15AnchoredAtom1815 chi)) ∨
      ((Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom1776 chi) ∨
      (Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom1779 chi))) ∨
      (((Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom1782 chi) ∨
      (Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom1816 chi)) ∨
      ((¬Fin15AnchoredAtom4798 chi ∧
      Fin15AnchoredAtom1776 chi ∧
      Fin15AnchoredAtom1777 chi ∧
      Fin15AnchoredAtom1779 chi ∧
      Fin15AnchoredAtom1782 chi ∧
      Fin15AnchoredAtom1816 chi) ∨
      (Fin15AnchoredAtom4799 chi ∧
      ¬Fin15AnchoredAtom1778 chi))))) ∨
      (((((Fin15AnchoredAtom4799 chi ∧
      ¬Fin15AnchoredAtom1780 chi) ∨
      (Fin15AnchoredAtom4799 chi ∧
      ¬Fin15AnchoredAtom1817 chi)) ∨
      ((¬Fin15AnchoredAtom4799 chi ∧
      Fin15AnchoredAtom1776 chi ∧
      Fin15AnchoredAtom1778 chi ∧
      Fin15AnchoredAtom1780 chi ∧
      Fin15AnchoredAtom1783 chi ∧
      Fin15AnchoredAtom1817 chi) ∨
      (Fin15AnchoredAtom4800 chi ∧
      ¬Fin15AnchoredAtom1777 chi))) ∨
      (((Fin15AnchoredAtom4800 chi ∧
      ¬Fin15AnchoredAtom1778 chi) ∨
      (Fin15AnchoredAtom4800 chi ∧
      ¬Fin15AnchoredAtom1784 chi)) ∨
      ((¬Fin15AnchoredAtom4800 chi ∧
      Fin15AnchoredAtom1777 chi ∧
      Fin15AnchoredAtom1778 chi ∧
      Fin15AnchoredAtom1781 chi ∧
      Fin15AnchoredAtom1784 chi ∧
      Fin15AnchoredAtom1818 chi) ∨
      (Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom1779 chi)))) ∨
      ((((Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom1780 chi) ∨
      (Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom1781 chi)) ∨
      ((Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom1785 chi) ∨
      (Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom1819 chi))) ∨
      (((¬Fin15AnchoredAtom4801 chi ∧
      Fin15AnchoredAtom1779 chi ∧
      Fin15AnchoredAtom1780 chi ∧
      Fin15AnchoredAtom1781 chi ∧
      Fin15AnchoredAtom1785 chi ∧
      Fin15AnchoredAtom1819 chi) ∨
      (Fin15AnchoredAtom4802 chi ∧
      ¬Fin15AnchoredAtom1783 chi)) ∨
      ((Fin15AnchoredAtom4802 chi ∧
      ¬Fin15AnchoredAtom1785 chi) ∨
      (Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom1787 chi)))))) ∨
      ((((((Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom1788 chi) ∨
      (Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom1793 chi)) ∨
      ((Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom1799 chi) ∨
      (Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom1809 chi))) ∨
      (((¬Fin15AnchoredAtom4806 chi ∧
      Fin15AnchoredAtom1787 chi ∧
      Fin15AnchoredAtom1788 chi ∧
      Fin15AnchoredAtom1793 chi ∧
      Fin15AnchoredAtom1799 chi ∧
      Fin15AnchoredAtom1809 chi) ∨
      (Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom1787 chi)) ∨
      ((Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom1789 chi) ∨
      (Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom1800 chi)))) ∨
      ((((Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom1810 chi) ∨
      (¬Fin15AnchoredAtom4807 chi ∧
      Fin15AnchoredAtom1787 chi ∧
      Fin15AnchoredAtom1789 chi ∧
      Fin15AnchoredAtom1794 chi ∧
      Fin15AnchoredAtom1800 chi ∧
      Fin15AnchoredAtom1810 chi)) ∨
      ((Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom1788 chi) ∨
      (Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom1789 chi))) ∨
      (((Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom1801 chi) ∨
      (Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom1811 chi)) ∨
      ((¬Fin15AnchoredAtom4808 chi ∧
      Fin15AnchoredAtom1788 chi ∧
      Fin15AnchoredAtom1789 chi ∧
      Fin15AnchoredAtom1795 chi ∧
      Fin15AnchoredAtom1801 chi ∧
      Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom1793 chi))))) ∨
      (((((Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom1794 chi) ∨
      (Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom1795 chi)) ∨
      ((Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom1805 chi) ∨
      (Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom1815 chi))) ∨
      (((¬Fin15AnchoredAtom4812 chi ∧
      Fin15AnchoredAtom1793 chi ∧
      Fin15AnchoredAtom1794 chi ∧
      Fin15AnchoredAtom1795 chi ∧
      Fin15AnchoredAtom1805 chi ∧
      Fin15AnchoredAtom1815 chi) ∨
      (Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom1799 chi)) ∨
      ((Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom1800 chi) ∨
      (Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom1801 chi)))) ∨
      ((((Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom1805 chi) ∨
      (Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom1819 chi)) ∨
      ((¬Fin15AnchoredAtom4816 chi ∧
      Fin15AnchoredAtom1799 chi ∧
      Fin15AnchoredAtom1800 chi ∧
      Fin15AnchoredAtom1801 chi ∧
      Fin15AnchoredAtom1805 chi ∧
      Fin15AnchoredAtom1819 chi) ∨
      (Fin15AnchoredAtom4818 chi ∧
      ¬Fin15AnchoredAtom1809 chi))) ∨
      (((Fin15AnchoredAtom4819 chi ∧
      ¬Fin15AnchoredAtom1810 chi) ∨
      (¬Fin15AnchoredAtom4819 chi ∧
      Fin15AnchoredAtom1806 chi ∧
      Fin15AnchoredAtom1808 chi ∧
      Fin15AnchoredAtom1810 chi ∧
      Fin15AnchoredAtom1813 chi ∧
      Fin15AnchoredAtom1817 chi)) ∨
      ((Fin15AnchoredAtom4820 chi ∧
      ¬Fin15AnchoredAtom1807 chi) ∨
      (Fin15AnchoredAtom4820 chi ∧
      ¬Fin15AnchoredAtom1808 chi))))))) ∨
      (((((((Fin15AnchoredAtom4820 chi ∧
      ¬Fin15AnchoredAtom1811 chi) ∨
      (Fin15AnchoredAtom4820 chi ∧
      ¬Fin15AnchoredAtom1818 chi)) ∨
      ((¬Fin15AnchoredAtom4820 chi ∧
      Fin15AnchoredAtom1807 chi ∧
      Fin15AnchoredAtom1808 chi ∧
      Fin15AnchoredAtom1811 chi ∧
      Fin15AnchoredAtom1814 chi ∧
      Fin15AnchoredAtom1818 chi) ∨
      (Fin15AnchoredAtom4821 chi ∧
      ¬Fin15AnchoredAtom1809 chi))) ∨
      (((Fin15AnchoredAtom4821 chi ∧
      ¬Fin15AnchoredAtom1810 chi) ∨
      (Fin15AnchoredAtom4821 chi ∧
      ¬Fin15AnchoredAtom1811 chi)) ∨
      ((Fin15AnchoredAtom4821 chi ∧
      ¬Fin15AnchoredAtom1815 chi) ∨
      (Fin15AnchoredAtom4821 chi ∧
      ¬Fin15AnchoredAtom1819 chi)))) ∨
      ((((¬Fin15AnchoredAtom4821 chi ∧
      Fin15AnchoredAtom1809 chi ∧
      Fin15AnchoredAtom1810 chi ∧
      Fin15AnchoredAtom1811 chi ∧
      Fin15AnchoredAtom1815 chi ∧
      Fin15AnchoredAtom1819 chi) ∨
      (Fin15AnchoredAtom4822 chi ∧
      ¬Fin15AnchoredAtom1812 chi)) ∨
      ((Fin15AnchoredAtom4822 chi ∧
      ¬Fin15AnchoredAtom1813 chi) ∨
      (Fin15AnchoredAtom4823 chi ∧
      ¬Fin15AnchoredAtom1818 chi))) ∨
      (((Fin15AnchoredAtom4823 chi ∧
      ¬Fin15AnchoredAtom1819 chi) ∨
      (Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2822 chi)) ∨
      ((Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2823 chi) ∨
      (Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2824 chi))))) ∨
      (((((Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2826 chi) ∨
      (Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2827 chi)) ∨
      ((Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom1838 chi ∧
      Fin15AnchoredAtom1893 chi ∧
      Fin15AnchoredAtom2113 chi ∧
      Fin15AnchoredAtom2828 chi) ∨
      (Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2829 chi))) ∨
      (((Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2830 chi) ∨
      (Fin15AnchoredAtom1821 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2831 chi)) ∨
      ((Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2832 chi) ∨
      (Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2833 chi)))) ∨
      ((((Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1825 chi ∧
      Fin15AnchoredAtom1844 chi ∧
      Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom2834 chi) ∨
      (Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2835 chi)) ∨
      ((Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2836 chi) ∨
      (Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom1847 chi ∧
      Fin15AnchoredAtom1902 chi ∧
      Fin15AnchoredAtom2122 chi ∧
      Fin15AnchoredAtom2837 chi))) ∨
      (((Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2838 chi) ∨
      (Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2839 chi)) ∨
      ((Fin15AnchoredAtom1822 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2840 chi) ∨
      (Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2841 chi)))))) ∨
      ((((((Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2843 chi) ∨
      (Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2844 chi)) ∨
      ((Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2846 chi) ∨
      (Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2847 chi))) ∨
      (((Fin15AnchoredAtom1823 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2848 chi) ∨
      (Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1825 chi ∧
      Fin15AnchoredAtom1859 chi ∧
      Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom2849 chi)) ∨
      ((Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2850 chi) ∨
      (Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2851 chi)))) ∨
      ((((Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2853 chi) ∨
      (Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2854 chi)) ∨
      ((Fin15AnchoredAtom1824 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2855 chi) ∨
      (Fin15AnchoredAtom1825 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1867 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2857 chi))) ∨
      (((Fin15AnchoredAtom1825 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1869 chi ∧
      Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom2144 chi ∧
      Fin15AnchoredAtom2859 chi) ∨
      (Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2862 chi)) ∨
      ((Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2864 chi) ∨
      (Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2865 chi))))) ∨
      (((((Fin15AnchoredAtom1826 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2866 chi) ∨
      (Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom1877 chi ∧
      Fin15AnchoredAtom1932 chi ∧
      Fin15AnchoredAtom2152 chi ∧
      Fin15AnchoredAtom2867 chi)) ∨
      ((Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2868 chi) ∨
      (Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2869 chi))) ∨
      (((Fin15AnchoredAtom1827 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2870 chi) ∨
      (Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1882 chi ∧
      Fin15AnchoredAtom1937 chi ∧
      Fin15AnchoredAtom2157 chi ∧
      Fin15AnchoredAtom2872 chi)) ∨
      ((Fin15AnchoredAtom1828 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1883 chi ∧
      Fin15AnchoredAtom1938 chi ∧
      Fin15AnchoredAtom2158 chi ∧
      Fin15AnchoredAtom2873 chi) ∨
      (Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2874 chi)))) ∨
      ((((Fin15AnchoredAtom1829 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2875 chi) ∨
      (Fin15AnchoredAtom1830 chi ∧
      Fin15AnchoredAtom1831 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2876 chi)) ∨
      ((Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2877 chi) ∨
      (Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2878 chi))) ∨
      (((Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2880 chi) ∨
      (Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2881 chi)) ∨
      ((Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2883 chi) ∨
      (Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2884 chi)))))))))) := by
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
                exact fin15Anchored_clause28017 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28018 chi hbad
                ·
                  exact fin15Anchored_clause28019 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28020 chi hbad
                ·
                  exact fin15Anchored_clause28021 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28022 chi hbad
                ·
                  exact fin15Anchored_clause28023 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28024 chi hbad
                ·
                  exact fin15Anchored_clause28025 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28026 chi hbad
                ·
                  exact fin15Anchored_clause28027 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28028 chi hbad
                ·
                  exact fin15Anchored_clause28029 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28030 chi hbad
                ·
                  exact fin15Anchored_clause28031 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28032 chi hbad
                ·
                  exact fin15Anchored_clause28033 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28034 chi hbad
                ·
                  exact fin15Anchored_clause28035 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28036 chi hbad
                ·
                  exact fin15Anchored_clause28037 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28038 chi hbad
                ·
                  exact fin15Anchored_clause28039 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28040 chi hbad
                ·
                  exact fin15Anchored_clause28041 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28042 chi hbad
                ·
                  exact fin15Anchored_clause28043 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28044 chi hbad
                ·
                  exact fin15Anchored_clause28045 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28046 chi hbad
                ·
                  exact fin15Anchored_clause28047 chi hbad
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
                  exact fin15Anchored_clause28048 chi hbad
                ·
                  exact fin15Anchored_clause28049 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28050 chi hbad
                ·
                  exact fin15Anchored_clause28051 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28052 chi hbad
                ·
                  exact fin15Anchored_clause28053 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28054 chi hbad
                ·
                  exact fin15Anchored_clause28055 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28056 chi hbad
                ·
                  exact fin15Anchored_clause28057 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28058 chi hbad
                ·
                  exact fin15Anchored_clause28059 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28060 chi hbad
                ·
                  exact fin15Anchored_clause28061 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28062 chi hbad
                ·
                  exact fin15Anchored_clause28063 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28064 chi hbad
                ·
                  exact fin15Anchored_clause28065 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28066 chi hbad
                ·
                  exact fin15Anchored_clause28067 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28068 chi hbad
                ·
                  exact fin15Anchored_clause28069 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28070 chi hbad
                ·
                  exact fin15Anchored_clause28071 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28072 chi hbad
                ·
                  exact fin15Anchored_clause28073 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28074 chi hbad
                ·
                  exact fin15Anchored_clause28075 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28076 chi hbad
                ·
                  exact fin15Anchored_clause28077 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28078 chi hbad
                ·
                  exact fin15Anchored_clause28079 chi hbad
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
                exact fin15Anchored_clause28080 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28081 chi hbad
                ·
                  exact fin15Anchored_clause28082 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28083 chi hbad
                ·
                  exact fin15Anchored_clause28084 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28085 chi hbad
                ·
                  exact fin15Anchored_clause28086 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28087 chi hbad
                ·
                  exact fin15Anchored_clause28088 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28089 chi hbad
                ·
                  exact fin15Anchored_clause28090 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28091 chi hbad
                ·
                  exact fin15Anchored_clause28092 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28093 chi hbad
                ·
                  exact fin15Anchored_clause28094 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28095 chi hbad
                ·
                  exact fin15Anchored_clause28096 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28097 chi hbad
                ·
                  exact fin15Anchored_clause28098 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28099 chi hbad
                ·
                  exact fin15Anchored_clause28100 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28101 chi hbad
                ·
                  exact fin15Anchored_clause28102 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28103 chi hbad
                ·
                  exact fin15Anchored_clause28104 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28105 chi hbad
                ·
                  exact fin15Anchored_clause28106 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28107 chi hbad
                ·
                  exact fin15Anchored_clause28108 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28109 chi hbad
                ·
                  exact fin15Anchored_clause28110 chi hbad
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
                  exact fin15Anchored_clause28111 chi hbad
                ·
                  exact fin15Anchored_clause28112 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28113 chi hbad
                ·
                  exact fin15Anchored_clause28114 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28115 chi hbad
                ·
                  exact fin15Anchored_clause28116 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28117 chi hbad
                ·
                  exact fin15Anchored_clause28118 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28119 chi hbad
                ·
                  exact fin15Anchored_clause28120 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28121 chi hbad
                ·
                  exact fin15Anchored_clause28122 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28123 chi hbad
                ·
                  exact fin15Anchored_clause28124 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28125 chi hbad
                ·
                  exact fin15Anchored_clause28126 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28127 chi hbad
                ·
                  exact fin15Anchored_clause28128 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28129 chi hbad
                ·
                  exact fin15Anchored_clause28130 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28131 chi hbad
                ·
                  exact fin15Anchored_clause28132 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28133 chi hbad
                ·
                  exact fin15Anchored_clause28134 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28135 chi hbad
                ·
                  exact fin15Anchored_clause28136 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28137 chi hbad
                ·
                  exact fin15Anchored_clause28138 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28139 chi hbad
                ·
                  exact fin15Anchored_clause28140 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28141 chi hbad
                ·
                  exact fin15Anchored_clause28142 chi hbad
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
                exact fin15Anchored_clause28143 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28144 chi hbad
                ·
                  exact fin15Anchored_clause28145 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28146 chi hbad
                ·
                  exact fin15Anchored_clause28147 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28148 chi hbad
                ·
                  exact fin15Anchored_clause28149 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28150 chi hbad
                ·
                  exact fin15Anchored_clause28151 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28152 chi hbad
                ·
                  exact fin15Anchored_clause28153 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28154 chi hbad
                ·
                  exact fin15Anchored_clause28155 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28156 chi hbad
                ·
                  exact fin15Anchored_clause28157 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28158 chi hbad
                ·
                  exact fin15Anchored_clause28159 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28160 chi hbad
                ·
                  exact fin15Anchored_clause28161 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28162 chi hbad
                ·
                  exact fin15Anchored_clause28163 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28164 chi hbad
                ·
                  exact fin15Anchored_clause28165 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28166 chi hbad
                ·
                  exact fin15Anchored_clause28167 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28168 chi hbad
                ·
                  exact fin15Anchored_clause28169 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28170 chi hbad
                ·
                  exact fin15Anchored_clause28171 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28172 chi hbad
                ·
                  exact fin15Anchored_clause28173 chi hbad
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
                  exact fin15Anchored_clause28174 chi hbad
                ·
                  exact fin15Anchored_clause28175 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28176 chi hbad
                ·
                  exact fin15Anchored_clause28177 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28178 chi hbad
                ·
                  exact fin15Anchored_clause28179 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28180 chi hbad
                ·
                  exact fin15Anchored_clause28181 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28182 chi hbad
                ·
                  exact fin15Anchored_clause28183 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28184 chi hbad
                ·
                  exact fin15Anchored_clause28185 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28186 chi hbad
                ·
                  exact fin15Anchored_clause28187 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28188 chi hbad
                ·
                  exact fin15Anchored_clause28189 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28190 chi hbad
                ·
                  exact fin15Anchored_clause28191 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28192 chi hbad
                ·
                  exact fin15Anchored_clause28193 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28194 chi hbad
                ·
                  exact fin15Anchored_clause28195 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28196 chi hbad
                ·
                  exact fin15Anchored_clause28197 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28198 chi hbad
                ·
                  exact fin15Anchored_clause28199 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28200 chi hbad
                ·
                  exact fin15Anchored_clause28201 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28202 chi hbad
                ·
                  exact fin15Anchored_clause28203 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28204 chi hbad
                ·
                  exact fin15Anchored_clause28205 chi hbad
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
                  exact fin15Anchored_clause28206 chi hbad
                ·
                  exact fin15Anchored_clause28207 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28208 chi hbad
                ·
                  exact fin15Anchored_clause28209 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28210 chi hbad
                ·
                  exact fin15Anchored_clause28211 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28212 chi hbad
                ·
                  exact fin15Anchored_clause28213 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28214 chi hbad
                ·
                  exact fin15Anchored_clause28215 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28216 chi hbad
                ·
                  exact fin15Anchored_clause28217 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28218 chi hbad
                ·
                  exact fin15Anchored_clause28219 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28220 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28221 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28222 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28223 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28224 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28225 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28226 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28227 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28228 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28229 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28230 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28231 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28232 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28233 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28234 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28235 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28236 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28237 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28238 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28239 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28240 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28241 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28242 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28243 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28244 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28245 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28246 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28247 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28248 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28249 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28250 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28251 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28252 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28253 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28254 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28255 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28256 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28257 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28258 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28259 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28260 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28261 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28262 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28263 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28264 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28265 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28266 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28267 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28268 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28269 chi hnoStrong hbad

end ErdosSzekeres

end
