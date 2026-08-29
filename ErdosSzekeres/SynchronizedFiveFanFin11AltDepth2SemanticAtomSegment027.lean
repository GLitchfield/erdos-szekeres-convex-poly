module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 027. -/

def SynchronizedFiveFanFin11OriginalAtom1592 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 3, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1593 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 3, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1594 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 3, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1595 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 7} ∧
    ¬IsCapSet chi {0, 4, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1596 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 8} ∧
    ¬IsCapSet chi {0, 4, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1597 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 9} ∧
    ¬IsCapSet chi {0, 4, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1598 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 10} ∧
    ¬IsCapSet chi {0, 4, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1599 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 8} ∧
    ¬IsCapSet chi {0, 4, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1600 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 9} ∧
    ¬IsCapSet chi {0, 4, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1601 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 10} ∧
    ¬IsCapSet chi {0, 4, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1602 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 9} ∧
    ¬IsCapSet chi {0, 4, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1603 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 10} ∧
    ¬IsCapSet chi {0, 4, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1604 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 10} ∧
    ¬IsCapSet chi {0, 4, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1605 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 8} ∧
    ¬IsCapSet chi {0, 4, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1606 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 9} ∧
    ¬IsCapSet chi {0, 4, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1607 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 10} ∧
    ¬IsCapSet chi {0, 4, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1608 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 9} ∧
    ¬IsCapSet chi {0, 4, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1609 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 10} ∧
    ¬IsCapSet chi {0, 4, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1610 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 10} ∧
    ¬IsCapSet chi {0, 4, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1611 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 9} ∧
    ¬IsCapSet chi {0, 4, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1612 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 4, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1613 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 4, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1614 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 4, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1615 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 8} ∧
    ¬IsCapSet chi {0, 5, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1616 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 9} ∧
    ¬IsCapSet chi {0, 5, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1617 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 10} ∧
    ¬IsCapSet chi {0, 5, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1618 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 9} ∧
    ¬IsCapSet chi {0, 5, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1619 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 10} ∧
    ¬IsCapSet chi {0, 5, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1620 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 10} ∧
    ¬IsCapSet chi {0, 5, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1621 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 9} ∧
    ¬IsCapSet chi {0, 5, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1622 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 5, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1623 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 5, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1624 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 5, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1625 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 9} ∧
    ¬IsCapSet chi {0, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1626 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1627 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1628 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1629 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1630 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 5} ∧
    ¬IsCapSet chi {1, 2, 3, 4, 5}

def SynchronizedFiveFanFin11OriginalAtom1631 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 6} ∧
    ¬IsCapSet chi {1, 2, 3, 4, 6}

def SynchronizedFiveFanFin11OriginalAtom1632 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 7} ∧
    ¬IsCapSet chi {1, 2, 3, 4, 7}

def SynchronizedFiveFanFin11OriginalAtom1633 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 8} ∧
    ¬IsCapSet chi {1, 2, 3, 4, 8}

def SynchronizedFiveFanFin11OriginalAtom1634 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 9} ∧
    ¬IsCapSet chi {1, 2, 3, 4, 9}

def SynchronizedFiveFanFin11OriginalAtom1635 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 4, 10}

def SynchronizedFiveFanFin11OriginalAtom1636 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 6} ∧
    ¬IsCapSet chi {1, 2, 3, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1637 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 7} ∧
    ¬IsCapSet chi {1, 2, 3, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1638 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 8} ∧
    ¬IsCapSet chi {1, 2, 3, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1639 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 9} ∧
    ¬IsCapSet chi {1, 2, 3, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1640 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1641 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 7} ∧
    ¬IsCapSet chi {1, 2, 3, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1642 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 8} ∧
    ¬IsCapSet chi {1, 2, 3, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1643 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 9} ∧
    ¬IsCapSet chi {1, 2, 3, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1644 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1645 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 8} ∧
    ¬IsCapSet chi {1, 2, 3, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1646 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 9} ∧
    ¬IsCapSet chi {1, 2, 3, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1647 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1648 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 9} ∧
    ¬IsCapSet chi {1, 2, 3, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1649 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 8, 10}

end ErdosSzekeres

end
