module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 029. -/

def SynchronizedFiveFanFin11OriginalAtom1708 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 9} ∧
    ¬IsCapSet chi {1, 3, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1709 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 10} ∧
    ¬IsCapSet chi {1, 3, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1710 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 9, 10} ∧
    ¬IsCapSet chi {1, 3, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1711 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 8} ∧
    ¬IsCapSet chi {1, 3, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1712 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 9} ∧
    ¬IsCapSet chi {1, 3, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1713 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 10} ∧
    ¬IsCapSet chi {1, 3, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1714 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 9} ∧
    ¬IsCapSet chi {1, 3, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1715 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 10} ∧
    ¬IsCapSet chi {1, 3, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1716 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 9, 10} ∧
    ¬IsCapSet chi {1, 3, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1717 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 9} ∧
    ¬IsCapSet chi {1, 3, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1718 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 10} ∧
    ¬IsCapSet chi {1, 3, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1719 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 9, 10} ∧
    ¬IsCapSet chi {1, 3, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1720 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 3, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1721 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 7} ∧
    ¬IsCapSet chi {1, 4, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1722 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 8} ∧
    ¬IsCapSet chi {1, 4, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1723 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 9} ∧
    ¬IsCapSet chi {1, 4, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1724 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 10} ∧
    ¬IsCapSet chi {1, 4, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1725 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 8} ∧
    ¬IsCapSet chi {1, 4, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1726 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 9} ∧
    ¬IsCapSet chi {1, 4, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1727 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 10} ∧
    ¬IsCapSet chi {1, 4, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1728 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 9} ∧
    ¬IsCapSet chi {1, 4, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1729 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 10} ∧
    ¬IsCapSet chi {1, 4, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1730 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 9, 10} ∧
    ¬IsCapSet chi {1, 4, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1731 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 8} ∧
    ¬IsCapSet chi {1, 4, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1732 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 9} ∧
    ¬IsCapSet chi {1, 4, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1733 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 10} ∧
    ¬IsCapSet chi {1, 4, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1734 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 9} ∧
    ¬IsCapSet chi {1, 4, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1735 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 10} ∧
    ¬IsCapSet chi {1, 4, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1736 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 9, 10} ∧
    ¬IsCapSet chi {1, 4, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1737 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 9} ∧
    ¬IsCapSet chi {1, 4, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1738 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 10} ∧
    ¬IsCapSet chi {1, 4, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1739 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 9, 10} ∧
    ¬IsCapSet chi {1, 4, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1740 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 4, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1741 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 8} ∧
    ¬IsCapSet chi {1, 5, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1742 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 9} ∧
    ¬IsCapSet chi {1, 5, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1743 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 10} ∧
    ¬IsCapSet chi {1, 5, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1744 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 9} ∧
    ¬IsCapSet chi {1, 5, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1745 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 10} ∧
    ¬IsCapSet chi {1, 5, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1746 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 9, 10} ∧
    ¬IsCapSet chi {1, 5, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1747 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 9} ∧
    ¬IsCapSet chi {1, 5, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1748 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 10} ∧
    ¬IsCapSet chi {1, 5, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1749 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 9, 10} ∧
    ¬IsCapSet chi {1, 5, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1750 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 5, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1751 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 9} ∧
    ¬IsCapSet chi {1, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1752 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 10} ∧
    ¬IsCapSet chi {1, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1753 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {1, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1754 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1755 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1756 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 6} ∧
    ¬IsCapSet chi {2, 3, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1757 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 7} ∧
    ¬IsCapSet chi {2, 3, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1758 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 8} ∧
    ¬IsCapSet chi {2, 3, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1759 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 9} ∧
    ¬IsCapSet chi {2, 3, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1760 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 10} ∧
    ¬IsCapSet chi {2, 3, 4, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1761 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 7} ∧
    ¬IsCapSet chi {2, 3, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1762 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 8} ∧
    ¬IsCapSet chi {2, 3, 4, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1763 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 9} ∧
    ¬IsCapSet chi {2, 3, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1764 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 10} ∧
    ¬IsCapSet chi {2, 3, 4, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1765 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 8} ∧
    ¬IsCapSet chi {2, 3, 4, 7, 8}

end ErdosSzekeres

end
