module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 024. -/

def SynchronizedFiveFanFin11OriginalAtom1417 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {5, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1418 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {5, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1419 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {6, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1420 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 4} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 4}

def SynchronizedFiveFanFin11OriginalAtom1421 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 5} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 5}

def SynchronizedFiveFanFin11OriginalAtom1422 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 6} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 6}

def SynchronizedFiveFanFin11OriginalAtom1423 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 7} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 7}

def SynchronizedFiveFanFin11OriginalAtom1424 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 8} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 8}

def SynchronizedFiveFanFin11OriginalAtom1425 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 9}

def SynchronizedFiveFanFin11OriginalAtom1426 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 10}

def SynchronizedFiveFanFin11OriginalAtom1427 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 5} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 5}

def SynchronizedFiveFanFin11OriginalAtom1428 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 6} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 6}

def SynchronizedFiveFanFin11OriginalAtom1429 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 7} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 7}

def SynchronizedFiveFanFin11OriginalAtom1430 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 8} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 8}

def SynchronizedFiveFanFin11OriginalAtom1431 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 9}

def SynchronizedFiveFanFin11OriginalAtom1432 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 10}

def SynchronizedFiveFanFin11OriginalAtom1433 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 6} ∧
    ¬IsCapSet chi {0, 1, 2, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1434 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 7} ∧
    ¬IsCapSet chi {0, 1, 2, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1435 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 8} ∧
    ¬IsCapSet chi {0, 1, 2, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1436 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1437 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1438 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 7} ∧
    ¬IsCapSet chi {0, 1, 2, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1439 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 8} ∧
    ¬IsCapSet chi {0, 1, 2, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1440 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1441 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1442 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 8} ∧
    ¬IsCapSet chi {0, 1, 2, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1443 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1444 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1445 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1446 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1447 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1448 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 5} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 5}

def SynchronizedFiveFanFin11OriginalAtom1449 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 6} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 6}

def SynchronizedFiveFanFin11OriginalAtom1450 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 7} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 7}

def SynchronizedFiveFanFin11OriginalAtom1451 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 8} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 8}

def SynchronizedFiveFanFin11OriginalAtom1452 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 9} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 9}

def SynchronizedFiveFanFin11OriginalAtom1453 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 10}

def SynchronizedFiveFanFin11OriginalAtom1454 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 6} ∧
    ¬IsCapSet chi {0, 1, 3, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1455 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 7} ∧
    ¬IsCapSet chi {0, 1, 3, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1456 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 8} ∧
    ¬IsCapSet chi {0, 1, 3, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1457 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 9} ∧
    ¬IsCapSet chi {0, 1, 3, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1458 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1459 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 7} ∧
    ¬IsCapSet chi {0, 1, 3, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1460 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 8} ∧
    ¬IsCapSet chi {0, 1, 3, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1461 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 9} ∧
    ¬IsCapSet chi {0, 1, 3, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1462 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1463 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 8} ∧
    ¬IsCapSet chi {0, 1, 3, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1464 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 9} ∧
    ¬IsCapSet chi {0, 1, 3, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1465 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1466 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 9} ∧
    ¬IsCapSet chi {0, 1, 3, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1467 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1468 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1469 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 6} ∧
    ¬IsCapSet chi {0, 1, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1470 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 7} ∧
    ¬IsCapSet chi {0, 1, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1471 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 8} ∧
    ¬IsCapSet chi {0, 1, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1472 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 9} ∧
    ¬IsCapSet chi {0, 1, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1473 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 10} ∧
    ¬IsCapSet chi {0, 1, 4, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1474 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 7} ∧
    ¬IsCapSet chi {0, 1, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1475 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 8} ∧
    ¬IsCapSet chi {0, 1, 4, 6, 8}

end ErdosSzekeres

end
