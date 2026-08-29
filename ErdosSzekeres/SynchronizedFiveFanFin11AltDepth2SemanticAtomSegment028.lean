module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 028. -/

def SynchronizedFiveFanFin11OriginalAtom1650 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1651 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 6} ∧
    ¬IsCapSet chi {1, 2, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1652 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 7} ∧
    ¬IsCapSet chi {1, 2, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1653 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 8} ∧
    ¬IsCapSet chi {1, 2, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1654 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 9} ∧
    ¬IsCapSet chi {1, 2, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1655 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 10} ∧
    ¬IsCapSet chi {1, 2, 4, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1656 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 7} ∧
    ¬IsCapSet chi {1, 2, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1657 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 8} ∧
    ¬IsCapSet chi {1, 2, 4, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1658 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 9} ∧
    ¬IsCapSet chi {1, 2, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1659 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 10} ∧
    ¬IsCapSet chi {1, 2, 4, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1660 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 8} ∧
    ¬IsCapSet chi {1, 2, 4, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1661 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 9} ∧
    ¬IsCapSet chi {1, 2, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1662 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 10} ∧
    ¬IsCapSet chi {1, 2, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1663 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 9} ∧
    ¬IsCapSet chi {1, 2, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1664 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 10} ∧
    ¬IsCapSet chi {1, 2, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1665 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1666 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 7} ∧
    ¬IsCapSet chi {1, 2, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1667 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 8} ∧
    ¬IsCapSet chi {1, 2, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1668 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 9} ∧
    ¬IsCapSet chi {1, 2, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1669 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 10} ∧
    ¬IsCapSet chi {1, 2, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1670 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 8} ∧
    ¬IsCapSet chi {1, 2, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1671 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 9} ∧
    ¬IsCapSet chi {1, 2, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1672 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 10} ∧
    ¬IsCapSet chi {1, 2, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1673 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 9} ∧
    ¬IsCapSet chi {1, 2, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1674 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 10} ∧
    ¬IsCapSet chi {1, 2, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1675 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1676 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 8} ∧
    ¬IsCapSet chi {1, 2, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1677 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 9} ∧
    ¬IsCapSet chi {1, 2, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1678 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 10} ∧
    ¬IsCapSet chi {1, 2, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1679 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 9} ∧
    ¬IsCapSet chi {1, 2, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1680 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 10} ∧
    ¬IsCapSet chi {1, 2, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1681 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1682 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 8, 9} ∧
    ¬IsCapSet chi {1, 2, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1683 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 8, 10} ∧
    ¬IsCapSet chi {1, 2, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1684 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1685 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1686 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 6} ∧
    ¬IsCapSet chi {1, 3, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1687 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 7} ∧
    ¬IsCapSet chi {1, 3, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1688 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 8} ∧
    ¬IsCapSet chi {1, 3, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1689 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 9} ∧
    ¬IsCapSet chi {1, 3, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1690 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 10} ∧
    ¬IsCapSet chi {1, 3, 4, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1691 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 7} ∧
    ¬IsCapSet chi {1, 3, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1692 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 8} ∧
    ¬IsCapSet chi {1, 3, 4, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1693 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 9} ∧
    ¬IsCapSet chi {1, 3, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1694 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 10} ∧
    ¬IsCapSet chi {1, 3, 4, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1695 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 8} ∧
    ¬IsCapSet chi {1, 3, 4, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1696 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 9} ∧
    ¬IsCapSet chi {1, 3, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1697 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 10} ∧
    ¬IsCapSet chi {1, 3, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1698 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 9} ∧
    ¬IsCapSet chi {1, 3, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1699 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 10} ∧
    ¬IsCapSet chi {1, 3, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1700 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 9, 10} ∧
    ¬IsCapSet chi {1, 3, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1701 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 7} ∧
    ¬IsCapSet chi {1, 3, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1702 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 8} ∧
    ¬IsCapSet chi {1, 3, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1703 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 9} ∧
    ¬IsCapSet chi {1, 3, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1704 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 10} ∧
    ¬IsCapSet chi {1, 3, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1705 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 8} ∧
    ¬IsCapSet chi {1, 3, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1706 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 9} ∧
    ¬IsCapSet chi {1, 3, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1707 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 10} ∧
    ¬IsCapSet chi {1, 3, 5, 7, 10}

end ErdosSzekeres

end
