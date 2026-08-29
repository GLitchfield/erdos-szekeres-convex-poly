module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 022. -/

def SynchronizedFiveFanFin11OriginalAtom1299 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 7} ∧
    ¬IsCupSet chi {2, 3, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1300 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 8} ∧
    ¬IsCupSet chi {2, 3, 4, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1301 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 9} ∧
    ¬IsCupSet chi {2, 3, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1302 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 10} ∧
    ¬IsCupSet chi {2, 3, 4, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1303 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 8} ∧
    ¬IsCupSet chi {2, 3, 4, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1304 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 9} ∧
    ¬IsCupSet chi {2, 3, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1305 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 10} ∧
    ¬IsCupSet chi {2, 3, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1306 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 9} ∧
    ¬IsCupSet chi {2, 3, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1307 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 10} ∧
    ¬IsCupSet chi {2, 3, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1308 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 10} ∧
    ¬IsCupSet chi {2, 3, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1309 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 7} ∧
    ¬IsCupSet chi {2, 3, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1310 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 8} ∧
    ¬IsCupSet chi {2, 3, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1311 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 9} ∧
    ¬IsCupSet chi {2, 3, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1312 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 10} ∧
    ¬IsCupSet chi {2, 3, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1313 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 8} ∧
    ¬IsCupSet chi {2, 3, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1314 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 9} ∧
    ¬IsCupSet chi {2, 3, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1315 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 10} ∧
    ¬IsCupSet chi {2, 3, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1316 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 9} ∧
    ¬IsCupSet chi {2, 3, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1317 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 10} ∧
    ¬IsCupSet chi {2, 3, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1318 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 10} ∧
    ¬IsCupSet chi {2, 3, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1319 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 8} ∧
    ¬IsCupSet chi {2, 3, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1320 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 9} ∧
    ¬IsCupSet chi {2, 3, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1321 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 10} ∧
    ¬IsCupSet chi {2, 3, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1322 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 9} ∧
    ¬IsCupSet chi {2, 3, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1323 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 10} ∧
    ¬IsCupSet chi {2, 3, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1324 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 10} ∧
    ¬IsCupSet chi {2, 3, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1325 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 9} ∧
    ¬IsCupSet chi {2, 3, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1326 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 10} ∧
    ¬IsCupSet chi {2, 3, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1327 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 10} ∧
    ¬IsCupSet chi {2, 3, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1328 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 9, 10} ∧
    ¬IsCupSet chi {2, 3, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1329 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 7} ∧
    ¬IsCupSet chi {2, 4, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1330 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 8} ∧
    ¬IsCupSet chi {2, 4, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1331 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 9} ∧
    ¬IsCupSet chi {2, 4, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1332 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 10} ∧
    ¬IsCupSet chi {2, 4, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1333 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 8} ∧
    ¬IsCupSet chi {2, 4, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1334 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 9} ∧
    ¬IsCupSet chi {2, 4, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1335 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 10} ∧
    ¬IsCupSet chi {2, 4, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1336 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 9} ∧
    ¬IsCupSet chi {2, 4, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1337 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 10} ∧
    ¬IsCupSet chi {2, 4, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1338 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 10} ∧
    ¬IsCupSet chi {2, 4, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1339 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 8} ∧
    ¬IsCupSet chi {2, 4, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1340 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 9} ∧
    ¬IsCupSet chi {2, 4, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1341 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 10} ∧
    ¬IsCupSet chi {2, 4, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1342 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 9} ∧
    ¬IsCupSet chi {2, 4, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1343 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 10} ∧
    ¬IsCupSet chi {2, 4, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1344 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 10} ∧
    ¬IsCupSet chi {2, 4, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1345 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 9} ∧
    ¬IsCupSet chi {2, 4, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1346 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 10} ∧
    ¬IsCupSet chi {2, 4, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1347 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 10} ∧
    ¬IsCupSet chi {2, 4, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1348 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 9, 10} ∧
    ¬IsCupSet chi {2, 4, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1349 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 8} ∧
    ¬IsCupSet chi {2, 5, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1350 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 9} ∧
    ¬IsCupSet chi {2, 5, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1351 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 10} ∧
    ¬IsCupSet chi {2, 5, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1352 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 9} ∧
    ¬IsCupSet chi {2, 5, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1353 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 10} ∧
    ¬IsCupSet chi {2, 5, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1354 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 10} ∧
    ¬IsCupSet chi {2, 5, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1355 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 9} ∧
    ¬IsCupSet chi {2, 5, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1356 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 10} ∧
    ¬IsCupSet chi {2, 5, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1357 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 10} ∧
    ¬IsCupSet chi {2, 5, 7, 9, 10}

end ErdosSzekeres

end
