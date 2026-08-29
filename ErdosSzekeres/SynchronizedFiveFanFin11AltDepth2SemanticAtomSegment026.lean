module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 026. -/

def SynchronizedFiveFanFin11OriginalAtom1534 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 8} ∧
    ¬IsCapSet chi {0, 2, 4, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1535 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 9} ∧
    ¬IsCapSet chi {0, 2, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1536 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 10} ∧
    ¬IsCapSet chi {0, 2, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1537 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 9} ∧
    ¬IsCapSet chi {0, 2, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1538 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 10} ∧
    ¬IsCapSet chi {0, 2, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1539 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1540 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 7} ∧
    ¬IsCapSet chi {0, 2, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1541 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 8} ∧
    ¬IsCapSet chi {0, 2, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1542 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 9} ∧
    ¬IsCapSet chi {0, 2, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1543 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 10} ∧
    ¬IsCapSet chi {0, 2, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1544 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 8} ∧
    ¬IsCapSet chi {0, 2, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1545 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 9} ∧
    ¬IsCapSet chi {0, 2, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1546 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 10} ∧
    ¬IsCapSet chi {0, 2, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1547 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 9} ∧
    ¬IsCapSet chi {0, 2, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1548 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 10} ∧
    ¬IsCapSet chi {0, 2, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1549 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1550 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 8} ∧
    ¬IsCapSet chi {0, 2, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1551 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 9} ∧
    ¬IsCapSet chi {0, 2, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1552 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 10} ∧
    ¬IsCapSet chi {0, 2, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1553 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 9} ∧
    ¬IsCapSet chi {0, 2, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1554 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 10} ∧
    ¬IsCapSet chi {0, 2, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1555 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1556 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 9} ∧
    ¬IsCapSet chi {0, 2, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1557 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 2, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1558 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1559 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1560 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 6} ∧
    ¬IsCapSet chi {0, 3, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1561 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 7} ∧
    ¬IsCapSet chi {0, 3, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1562 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 8} ∧
    ¬IsCapSet chi {0, 3, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1563 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 9} ∧
    ¬IsCapSet chi {0, 3, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1564 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 10} ∧
    ¬IsCapSet chi {0, 3, 4, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1565 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 7} ∧
    ¬IsCapSet chi {0, 3, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1566 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 8} ∧
    ¬IsCapSet chi {0, 3, 4, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1567 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 9} ∧
    ¬IsCapSet chi {0, 3, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1568 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 10} ∧
    ¬IsCapSet chi {0, 3, 4, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1569 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 8} ∧
    ¬IsCapSet chi {0, 3, 4, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1570 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 9} ∧
    ¬IsCapSet chi {0, 3, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1571 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 10} ∧
    ¬IsCapSet chi {0, 3, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1572 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 9} ∧
    ¬IsCapSet chi {0, 3, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1573 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 10} ∧
    ¬IsCapSet chi {0, 3, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1574 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 10} ∧
    ¬IsCapSet chi {0, 3, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1575 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 7} ∧
    ¬IsCapSet chi {0, 3, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1576 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 8} ∧
    ¬IsCapSet chi {0, 3, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1577 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 9} ∧
    ¬IsCapSet chi {0, 3, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1578 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 10} ∧
    ¬IsCapSet chi {0, 3, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1579 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 8} ∧
    ¬IsCapSet chi {0, 3, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1580 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 9} ∧
    ¬IsCapSet chi {0, 3, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1581 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 10} ∧
    ¬IsCapSet chi {0, 3, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1582 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 9} ∧
    ¬IsCapSet chi {0, 3, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1583 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 10} ∧
    ¬IsCapSet chi {0, 3, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1584 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 10} ∧
    ¬IsCapSet chi {0, 3, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1585 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 8} ∧
    ¬IsCapSet chi {0, 3, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1586 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 9} ∧
    ¬IsCapSet chi {0, 3, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1587 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 10} ∧
    ¬IsCapSet chi {0, 3, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1588 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 9} ∧
    ¬IsCapSet chi {0, 3, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1589 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 10} ∧
    ¬IsCapSet chi {0, 3, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1590 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 10} ∧
    ¬IsCapSet chi {0, 3, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1591 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 9} ∧
    ¬IsCapSet chi {0, 3, 7, 8, 9}

end ErdosSzekeres

end
