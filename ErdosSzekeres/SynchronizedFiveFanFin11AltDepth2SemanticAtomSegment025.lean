module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 025. -/

def SynchronizedFiveFanFin11OriginalAtom1476 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 9} ∧
    ¬IsCapSet chi {0, 1, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1477 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 10} ∧
    ¬IsCapSet chi {0, 1, 4, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1478 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 8} ∧
    ¬IsCapSet chi {0, 1, 4, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1479 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 9} ∧
    ¬IsCapSet chi {0, 1, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1480 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 10} ∧
    ¬IsCapSet chi {0, 1, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1481 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 9} ∧
    ¬IsCapSet chi {0, 1, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1482 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1483 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1484 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 7} ∧
    ¬IsCapSet chi {0, 1, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1485 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 8} ∧
    ¬IsCapSet chi {0, 1, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1486 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 9} ∧
    ¬IsCapSet chi {0, 1, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1487 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 10} ∧
    ¬IsCapSet chi {0, 1, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1488 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 8} ∧
    ¬IsCapSet chi {0, 1, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1489 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 9} ∧
    ¬IsCapSet chi {0, 1, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1490 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 10} ∧
    ¬IsCapSet chi {0, 1, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1491 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 9} ∧
    ¬IsCapSet chi {0, 1, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1492 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1493 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1494 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 8} ∧
    ¬IsCapSet chi {0, 1, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1495 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 9} ∧
    ¬IsCapSet chi {0, 1, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1496 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 10} ∧
    ¬IsCapSet chi {0, 1, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1497 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 9} ∧
    ¬IsCapSet chi {0, 1, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1498 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1499 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1500 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 8, 9} ∧
    ¬IsCapSet chi {0, 1, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1501 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1502 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1503 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1504 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 5} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 5}

def SynchronizedFiveFanFin11OriginalAtom1505 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 6} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 6}

def SynchronizedFiveFanFin11OriginalAtom1506 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 7} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 7}

def SynchronizedFiveFanFin11OriginalAtom1507 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 8} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 8}

def SynchronizedFiveFanFin11OriginalAtom1508 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 9} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 9}

def SynchronizedFiveFanFin11OriginalAtom1509 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 10}

def SynchronizedFiveFanFin11OriginalAtom1510 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 6} ∧
    ¬IsCapSet chi {0, 2, 3, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1511 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 7} ∧
    ¬IsCapSet chi {0, 2, 3, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1512 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 8} ∧
    ¬IsCapSet chi {0, 2, 3, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1513 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 9} ∧
    ¬IsCapSet chi {0, 2, 3, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1514 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1515 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 7} ∧
    ¬IsCapSet chi {0, 2, 3, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1516 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 8} ∧
    ¬IsCapSet chi {0, 2, 3, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1517 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 9} ∧
    ¬IsCapSet chi {0, 2, 3, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1518 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1519 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 8} ∧
    ¬IsCapSet chi {0, 2, 3, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1520 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 9} ∧
    ¬IsCapSet chi {0, 2, 3, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1521 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1522 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 9} ∧
    ¬IsCapSet chi {0, 2, 3, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1523 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1524 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1525 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 6} ∧
    ¬IsCapSet chi {0, 2, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1526 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 7} ∧
    ¬IsCapSet chi {0, 2, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1527 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 8} ∧
    ¬IsCapSet chi {0, 2, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1528 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 9} ∧
    ¬IsCapSet chi {0, 2, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1529 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 10} ∧
    ¬IsCapSet chi {0, 2, 4, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1530 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 7} ∧
    ¬IsCapSet chi {0, 2, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1531 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 8} ∧
    ¬IsCapSet chi {0, 2, 4, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1532 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 9} ∧
    ¬IsCapSet chi {0, 2, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1533 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 10} ∧
    ¬IsCapSet chi {0, 2, 4, 6, 10}

end ErdosSzekeres

end
