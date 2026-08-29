module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 019. -/

def SynchronizedFiveFanFin11OriginalAtom1122 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 10} ∧
    ¬IsCupSet chi {0, 3, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1123 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 8} ∧
    ¬IsCupSet chi {0, 3, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1124 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 9} ∧
    ¬IsCupSet chi {0, 3, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1125 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 10} ∧
    ¬IsCupSet chi {0, 3, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1126 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 9} ∧
    ¬IsCupSet chi {0, 3, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1127 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 10} ∧
    ¬IsCupSet chi {0, 3, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1128 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 10} ∧
    ¬IsCupSet chi {0, 3, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1129 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 9} ∧
    ¬IsCupSet chi {0, 3, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1130 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 10} ∧
    ¬IsCupSet chi {0, 3, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1131 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 10} ∧
    ¬IsCupSet chi {0, 3, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1132 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 3, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1133 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 7} ∧
    ¬IsCupSet chi {0, 4, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1134 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 8} ∧
    ¬IsCupSet chi {0, 4, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1135 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 9} ∧
    ¬IsCupSet chi {0, 4, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1136 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 10} ∧
    ¬IsCupSet chi {0, 4, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1137 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 8} ∧
    ¬IsCupSet chi {0, 4, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1138 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 9} ∧
    ¬IsCupSet chi {0, 4, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1139 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 10} ∧
    ¬IsCupSet chi {0, 4, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1140 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 9} ∧
    ¬IsCupSet chi {0, 4, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1141 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 10} ∧
    ¬IsCupSet chi {0, 4, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1142 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 10} ∧
    ¬IsCupSet chi {0, 4, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1143 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 8} ∧
    ¬IsCupSet chi {0, 4, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1144 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 9} ∧
    ¬IsCupSet chi {0, 4, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1145 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 10} ∧
    ¬IsCupSet chi {0, 4, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1146 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 9} ∧
    ¬IsCupSet chi {0, 4, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1147 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 10} ∧
    ¬IsCupSet chi {0, 4, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1148 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 10} ∧
    ¬IsCupSet chi {0, 4, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1149 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 9} ∧
    ¬IsCupSet chi {0, 4, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1150 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 10} ∧
    ¬IsCupSet chi {0, 4, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1151 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 10} ∧
    ¬IsCupSet chi {0, 4, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1152 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 4, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1153 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 8} ∧
    ¬IsCupSet chi {0, 5, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1154 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 9} ∧
    ¬IsCupSet chi {0, 5, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1155 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 10} ∧
    ¬IsCupSet chi {0, 5, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1156 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 9} ∧
    ¬IsCupSet chi {0, 5, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1157 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 10} ∧
    ¬IsCupSet chi {0, 5, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1158 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 10} ∧
    ¬IsCupSet chi {0, 5, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1159 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 9} ∧
    ¬IsCupSet chi {0, 5, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1160 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 10} ∧
    ¬IsCupSet chi {0, 5, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1161 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 10} ∧
    ¬IsCupSet chi {0, 5, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1162 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 5, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1163 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 9} ∧
    ¬IsCupSet chi {0, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1164 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 10} ∧
    ¬IsCupSet chi {0, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1165 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {0, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1166 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1167 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1168 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 5} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 5}

def SynchronizedFiveFanFin11OriginalAtom1169 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 6} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 6}

def SynchronizedFiveFanFin11OriginalAtom1170 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 7} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 7}

def SynchronizedFiveFanFin11OriginalAtom1171 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 8} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 8}

def SynchronizedFiveFanFin11OriginalAtom1172 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 9} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 9}

def SynchronizedFiveFanFin11OriginalAtom1173 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 10}

def SynchronizedFiveFanFin11OriginalAtom1174 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 6} ∧
    ¬IsCupSet chi {1, 2, 3, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1175 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 7} ∧
    ¬IsCupSet chi {1, 2, 3, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1176 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 8} ∧
    ¬IsCupSet chi {1, 2, 3, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1177 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 9} ∧
    ¬IsCupSet chi {1, 2, 3, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1178 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1179 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 7} ∧
    ¬IsCupSet chi {1, 2, 3, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1180 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 8} ∧
    ¬IsCupSet chi {1, 2, 3, 6, 8}

end ErdosSzekeres

end
