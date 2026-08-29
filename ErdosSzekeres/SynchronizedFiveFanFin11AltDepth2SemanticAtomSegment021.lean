module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 021. -/

def SynchronizedFiveFanFin11OriginalAtom1240 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 8} ∧
    ¬IsCupSet chi {1, 3, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1241 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 9} ∧
    ¬IsCupSet chi {1, 3, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1242 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 10} ∧
    ¬IsCupSet chi {1, 3, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1243 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 8} ∧
    ¬IsCupSet chi {1, 3, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1244 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 9} ∧
    ¬IsCupSet chi {1, 3, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1245 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 10} ∧
    ¬IsCupSet chi {1, 3, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1246 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 9} ∧
    ¬IsCupSet chi {1, 3, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1247 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 10} ∧
    ¬IsCupSet chi {1, 3, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1248 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 9, 10} ∧
    ¬IsCupSet chi {1, 3, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1249 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 8} ∧
    ¬IsCupSet chi {1, 3, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1250 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 9} ∧
    ¬IsCupSet chi {1, 3, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1251 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 10} ∧
    ¬IsCupSet chi {1, 3, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1252 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 9} ∧
    ¬IsCupSet chi {1, 3, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1253 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 10} ∧
    ¬IsCupSet chi {1, 3, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1254 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 9, 10} ∧
    ¬IsCupSet chi {1, 3, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1255 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 9} ∧
    ¬IsCupSet chi {1, 3, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1256 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 10} ∧
    ¬IsCupSet chi {1, 3, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1257 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 9, 10} ∧
    ¬IsCupSet chi {1, 3, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1258 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 9, 10} ∧
    ¬IsCupSet chi {1, 3, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1259 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 7} ∧
    ¬IsCupSet chi {1, 4, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1260 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 8} ∧
    ¬IsCupSet chi {1, 4, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1261 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 9} ∧
    ¬IsCupSet chi {1, 4, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1262 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 10} ∧
    ¬IsCupSet chi {1, 4, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1263 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 8} ∧
    ¬IsCupSet chi {1, 4, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1264 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 9} ∧
    ¬IsCupSet chi {1, 4, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1265 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 10} ∧
    ¬IsCupSet chi {1, 4, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1266 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 9} ∧
    ¬IsCupSet chi {1, 4, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1267 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 10} ∧
    ¬IsCupSet chi {1, 4, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1268 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 9, 10} ∧
    ¬IsCupSet chi {1, 4, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1269 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 8} ∧
    ¬IsCupSet chi {1, 4, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1270 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 9} ∧
    ¬IsCupSet chi {1, 4, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1271 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 10} ∧
    ¬IsCupSet chi {1, 4, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1272 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 9} ∧
    ¬IsCupSet chi {1, 4, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1273 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 10} ∧
    ¬IsCupSet chi {1, 4, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1274 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 9, 10} ∧
    ¬IsCupSet chi {1, 4, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1275 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 9} ∧
    ¬IsCupSet chi {1, 4, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1276 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 10} ∧
    ¬IsCupSet chi {1, 4, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1277 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 9, 10} ∧
    ¬IsCupSet chi {1, 4, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1278 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 9, 10} ∧
    ¬IsCupSet chi {1, 4, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1279 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 8} ∧
    ¬IsCupSet chi {1, 5, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1280 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 9} ∧
    ¬IsCupSet chi {1, 5, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1281 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 10} ∧
    ¬IsCupSet chi {1, 5, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1282 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 9} ∧
    ¬IsCupSet chi {1, 5, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1283 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 10} ∧
    ¬IsCupSet chi {1, 5, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1284 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 9, 10} ∧
    ¬IsCupSet chi {1, 5, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1285 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 9} ∧
    ¬IsCupSet chi {1, 5, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1286 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 10} ∧
    ¬IsCupSet chi {1, 5, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1287 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 9, 10} ∧
    ¬IsCupSet chi {1, 5, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1288 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 9, 10} ∧
    ¬IsCupSet chi {1, 5, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1289 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 9} ∧
    ¬IsCupSet chi {1, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1290 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 10} ∧
    ¬IsCupSet chi {1, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1291 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {1, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1292 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {1, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1293 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {1, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1294 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 6} ∧
    ¬IsCupSet chi {2, 3, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1295 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 7} ∧
    ¬IsCupSet chi {2, 3, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1296 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 8} ∧
    ¬IsCupSet chi {2, 3, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1297 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 9} ∧
    ¬IsCupSet chi {2, 3, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1298 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 10} ∧
    ¬IsCupSet chi {2, 3, 4, 5, 10}

end ErdosSzekeres

end
