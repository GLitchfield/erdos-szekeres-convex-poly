module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 020. -/

def SynchronizedFiveFanFin11OriginalAtom1181 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 9} ∧
    ¬IsCupSet chi {1, 2, 3, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1182 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1183 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 8} ∧
    ¬IsCupSet chi {1, 2, 3, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1184 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 9} ∧
    ¬IsCupSet chi {1, 2, 3, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1185 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1186 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 9} ∧
    ¬IsCupSet chi {1, 2, 3, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1187 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1188 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1189 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 6} ∧
    ¬IsCupSet chi {1, 2, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1190 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 7} ∧
    ¬IsCupSet chi {1, 2, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1191 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 8} ∧
    ¬IsCupSet chi {1, 2, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1192 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 9} ∧
    ¬IsCupSet chi {1, 2, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1193 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 10} ∧
    ¬IsCupSet chi {1, 2, 4, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1194 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 7} ∧
    ¬IsCupSet chi {1, 2, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1195 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 8} ∧
    ¬IsCupSet chi {1, 2, 4, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1196 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 9} ∧
    ¬IsCupSet chi {1, 2, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1197 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 10} ∧
    ¬IsCupSet chi {1, 2, 4, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1198 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 8} ∧
    ¬IsCupSet chi {1, 2, 4, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1199 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 9} ∧
    ¬IsCupSet chi {1, 2, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1200 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 10} ∧
    ¬IsCupSet chi {1, 2, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1201 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 9} ∧
    ¬IsCupSet chi {1, 2, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1202 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 10} ∧
    ¬IsCupSet chi {1, 2, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1203 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1204 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 7} ∧
    ¬IsCupSet chi {1, 2, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1205 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 8} ∧
    ¬IsCupSet chi {1, 2, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1206 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 9} ∧
    ¬IsCupSet chi {1, 2, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1207 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 10} ∧
    ¬IsCupSet chi {1, 2, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1208 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 8} ∧
    ¬IsCupSet chi {1, 2, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1209 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 9} ∧
    ¬IsCupSet chi {1, 2, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1210 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 10} ∧
    ¬IsCupSet chi {1, 2, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1211 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 9} ∧
    ¬IsCupSet chi {1, 2, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1212 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 10} ∧
    ¬IsCupSet chi {1, 2, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1213 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1214 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 8} ∧
    ¬IsCupSet chi {1, 2, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1215 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 9} ∧
    ¬IsCupSet chi {1, 2, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1216 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 10} ∧
    ¬IsCupSet chi {1, 2, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1217 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 9} ∧
    ¬IsCupSet chi {1, 2, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1218 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 10} ∧
    ¬IsCupSet chi {1, 2, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1219 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1220 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 8, 9} ∧
    ¬IsCupSet chi {1, 2, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1221 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 8, 10} ∧
    ¬IsCupSet chi {1, 2, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1222 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1223 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 8, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1224 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 6} ∧
    ¬IsCupSet chi {1, 3, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1225 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 7} ∧
    ¬IsCupSet chi {1, 3, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1226 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 8} ∧
    ¬IsCupSet chi {1, 3, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1227 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 9} ∧
    ¬IsCupSet chi {1, 3, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1228 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 10} ∧
    ¬IsCupSet chi {1, 3, 4, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1229 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 7} ∧
    ¬IsCupSet chi {1, 3, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1230 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 8} ∧
    ¬IsCupSet chi {1, 3, 4, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1231 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 9} ∧
    ¬IsCupSet chi {1, 3, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1232 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 10} ∧
    ¬IsCupSet chi {1, 3, 4, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1233 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 8} ∧
    ¬IsCupSet chi {1, 3, 4, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1234 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 9} ∧
    ¬IsCupSet chi {1, 3, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1235 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 10} ∧
    ¬IsCupSet chi {1, 3, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1236 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 9} ∧
    ¬IsCupSet chi {1, 3, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1237 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 10} ∧
    ¬IsCupSet chi {1, 3, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1238 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 9, 10} ∧
    ¬IsCupSet chi {1, 3, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1239 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 7} ∧
    ¬IsCupSet chi {1, 3, 5, 6, 7}

end ErdosSzekeres

end
