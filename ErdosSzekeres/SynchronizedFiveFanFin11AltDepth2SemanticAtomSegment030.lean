module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 030. -/

def SynchronizedFiveFanFin11OriginalAtom1766 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 9} ∧
    ¬IsCapSet chi {2, 3, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1767 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 10} ∧
    ¬IsCapSet chi {2, 3, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1768 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 9} ∧
    ¬IsCapSet chi {2, 3, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1769 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 10} ∧
    ¬IsCapSet chi {2, 3, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1770 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 10} ∧
    ¬IsCapSet chi {2, 3, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1771 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 7} ∧
    ¬IsCapSet chi {2, 3, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1772 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 8} ∧
    ¬IsCapSet chi {2, 3, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1773 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 9} ∧
    ¬IsCapSet chi {2, 3, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1774 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 10} ∧
    ¬IsCapSet chi {2, 3, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1775 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 8} ∧
    ¬IsCapSet chi {2, 3, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1776 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 9} ∧
    ¬IsCapSet chi {2, 3, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1777 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 10} ∧
    ¬IsCapSet chi {2, 3, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1778 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 9} ∧
    ¬IsCapSet chi {2, 3, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1779 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 10} ∧
    ¬IsCapSet chi {2, 3, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1780 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 10} ∧
    ¬IsCapSet chi {2, 3, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1781 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 8} ∧
    ¬IsCapSet chi {2, 3, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1782 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 9} ∧
    ¬IsCapSet chi {2, 3, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1783 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 10} ∧
    ¬IsCapSet chi {2, 3, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1784 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 9} ∧
    ¬IsCapSet chi {2, 3, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1785 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 10} ∧
    ¬IsCapSet chi {2, 3, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1786 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 10} ∧
    ¬IsCapSet chi {2, 3, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1787 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 9} ∧
    ¬IsCapSet chi {2, 3, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1788 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 10} ∧
    ¬IsCapSet chi {2, 3, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1789 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 10} ∧
    ¬IsCapSet chi {2, 3, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1790 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 9, 10} ∧
    ¬IsCapSet chi {2, 3, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1791 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 7} ∧
    ¬IsCapSet chi {2, 4, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1792 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 8} ∧
    ¬IsCapSet chi {2, 4, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1793 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 9} ∧
    ¬IsCapSet chi {2, 4, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1794 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 10} ∧
    ¬IsCapSet chi {2, 4, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1795 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 8} ∧
    ¬IsCapSet chi {2, 4, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1796 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 9} ∧
    ¬IsCapSet chi {2, 4, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1797 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 10} ∧
    ¬IsCapSet chi {2, 4, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1798 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 9} ∧
    ¬IsCapSet chi {2, 4, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1799 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 10} ∧
    ¬IsCapSet chi {2, 4, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1800 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 10} ∧
    ¬IsCapSet chi {2, 4, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1801 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 8} ∧
    ¬IsCapSet chi {2, 4, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1802 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 9} ∧
    ¬IsCapSet chi {2, 4, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1803 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 10} ∧
    ¬IsCapSet chi {2, 4, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1804 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 9} ∧
    ¬IsCapSet chi {2, 4, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1805 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 10} ∧
    ¬IsCapSet chi {2, 4, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1806 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 10} ∧
    ¬IsCapSet chi {2, 4, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1807 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 9} ∧
    ¬IsCapSet chi {2, 4, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1808 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 10} ∧
    ¬IsCapSet chi {2, 4, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1809 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 10} ∧
    ¬IsCapSet chi {2, 4, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1810 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 9, 10} ∧
    ¬IsCapSet chi {2, 4, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1811 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 8} ∧
    ¬IsCapSet chi {2, 5, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1812 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 9} ∧
    ¬IsCapSet chi {2, 5, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1813 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 10} ∧
    ¬IsCapSet chi {2, 5, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1814 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 9} ∧
    ¬IsCapSet chi {2, 5, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1815 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 10} ∧
    ¬IsCapSet chi {2, 5, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1816 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 10} ∧
    ¬IsCapSet chi {2, 5, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1817 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 9} ∧
    ¬IsCapSet chi {2, 5, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1818 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 10} ∧
    ¬IsCapSet chi {2, 5, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1819 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 10} ∧
    ¬IsCapSet chi {2, 5, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1820 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 9, 10} ∧
    ¬IsCapSet chi {2, 5, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1821 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 9} ∧
    ¬IsCapSet chi {2, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1822 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 10} ∧
    ¬IsCapSet chi {2, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1823 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {2, 6, 7, 9, 10}

end ErdosSzekeres

end
