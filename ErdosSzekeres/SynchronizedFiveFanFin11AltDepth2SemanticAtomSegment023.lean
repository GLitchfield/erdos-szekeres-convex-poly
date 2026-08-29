module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 023. -/

def SynchronizedFiveFanFin11OriginalAtom1358 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 9, 10} ∧
    ¬IsCupSet chi {2, 5, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1359 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 9} ∧
    ¬IsCupSet chi {2, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1360 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 10} ∧
    ¬IsCupSet chi {2, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1361 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {2, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1362 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {2, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1363 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {2, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1364 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 7} ∧
    ¬IsCupSet chi {3, 4, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1365 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 8} ∧
    ¬IsCupSet chi {3, 4, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1366 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 9} ∧
    ¬IsCupSet chi {3, 4, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1367 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 10} ∧
    ¬IsCupSet chi {3, 4, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1368 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 8} ∧
    ¬IsCupSet chi {3, 4, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1369 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 9} ∧
    ¬IsCupSet chi {3, 4, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1370 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 10} ∧
    ¬IsCupSet chi {3, 4, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1371 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 9} ∧
    ¬IsCupSet chi {3, 4, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1372 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 10} ∧
    ¬IsCupSet chi {3, 4, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1373 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 10} ∧
    ¬IsCupSet chi {3, 4, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1374 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 8} ∧
    ¬IsCupSet chi {3, 4, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1375 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 9} ∧
    ¬IsCupSet chi {3, 4, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1376 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 10} ∧
    ¬IsCupSet chi {3, 4, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1377 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 9} ∧
    ¬IsCupSet chi {3, 4, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1378 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 10} ∧
    ¬IsCupSet chi {3, 4, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1379 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 10} ∧
    ¬IsCupSet chi {3, 4, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1380 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 9} ∧
    ¬IsCupSet chi {3, 4, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1381 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 10} ∧
    ¬IsCupSet chi {3, 4, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1382 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 10} ∧
    ¬IsCupSet chi {3, 4, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1383 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 10} ∧
    ¬IsCupSet chi {3, 4, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1384 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 8} ∧
    ¬IsCupSet chi {3, 5, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1385 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 9} ∧
    ¬IsCupSet chi {3, 5, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1386 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 10} ∧
    ¬IsCupSet chi {3, 5, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1387 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 9} ∧
    ¬IsCupSet chi {3, 5, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1388 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 10} ∧
    ¬IsCupSet chi {3, 5, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1389 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 10} ∧
    ¬IsCupSet chi {3, 5, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1390 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 9} ∧
    ¬IsCupSet chi {3, 5, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1391 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 10} ∧
    ¬IsCupSet chi {3, 5, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1392 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 10} ∧
    ¬IsCupSet chi {3, 5, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1393 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 10} ∧
    ¬IsCupSet chi {3, 5, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1394 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 9} ∧
    ¬IsCupSet chi {3, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1395 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 10} ∧
    ¬IsCupSet chi {3, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1396 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {3, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1397 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {3, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1398 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {3, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1399 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 8} ∧
    ¬IsCupSet chi {4, 5, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1400 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 9} ∧
    ¬IsCupSet chi {4, 5, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1401 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 10} ∧
    ¬IsCupSet chi {4, 5, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1402 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 9} ∧
    ¬IsCupSet chi {4, 5, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1403 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 10} ∧
    ¬IsCupSet chi {4, 5, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1404 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 10} ∧
    ¬IsCupSet chi {4, 5, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1405 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 9} ∧
    ¬IsCupSet chi {4, 5, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1406 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 10} ∧
    ¬IsCupSet chi {4, 5, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1407 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 10} ∧
    ¬IsCupSet chi {4, 5, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1408 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 10} ∧
    ¬IsCupSet chi {4, 5, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1409 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 9} ∧
    ¬IsCupSet chi {4, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1410 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 10} ∧
    ¬IsCupSet chi {4, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1411 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {4, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1412 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {4, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1413 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {4, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1414 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 9} ∧
    ¬IsCupSet chi {5, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1415 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 10} ∧
    ¬IsCupSet chi {5, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1416 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {5, 6, 7, 9, 10}

end ErdosSzekeres

end
