module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 018. -/

def SynchronizedFiveFanFin11OriginalAtom1063 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 6} ∧
    ¬IsCupSet chi {0, 2, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1064 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 7} ∧
    ¬IsCupSet chi {0, 2, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1065 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 8} ∧
    ¬IsCupSet chi {0, 2, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1066 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 9} ∧
    ¬IsCupSet chi {0, 2, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1067 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 10} ∧
    ¬IsCupSet chi {0, 2, 4, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1068 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 7} ∧
    ¬IsCupSet chi {0, 2, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1069 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 8} ∧
    ¬IsCupSet chi {0, 2, 4, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1070 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 9} ∧
    ¬IsCupSet chi {0, 2, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1071 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 10} ∧
    ¬IsCupSet chi {0, 2, 4, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1072 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 8} ∧
    ¬IsCupSet chi {0, 2, 4, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1073 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 9} ∧
    ¬IsCupSet chi {0, 2, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1074 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 10} ∧
    ¬IsCupSet chi {0, 2, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1075 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 9} ∧
    ¬IsCupSet chi {0, 2, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1076 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 10} ∧
    ¬IsCupSet chi {0, 2, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1077 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1078 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 7} ∧
    ¬IsCupSet chi {0, 2, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1079 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 8} ∧
    ¬IsCupSet chi {0, 2, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1080 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 9} ∧
    ¬IsCupSet chi {0, 2, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1081 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 10} ∧
    ¬IsCupSet chi {0, 2, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1082 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 8} ∧
    ¬IsCupSet chi {0, 2, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1083 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 9} ∧
    ¬IsCupSet chi {0, 2, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1084 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 10} ∧
    ¬IsCupSet chi {0, 2, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1085 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 9} ∧
    ¬IsCupSet chi {0, 2, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1086 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 10} ∧
    ¬IsCupSet chi {0, 2, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1087 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1088 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 8} ∧
    ¬IsCupSet chi {0, 2, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1089 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 9} ∧
    ¬IsCupSet chi {0, 2, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1090 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 10} ∧
    ¬IsCupSet chi {0, 2, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1091 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 9} ∧
    ¬IsCupSet chi {0, 2, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1092 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 10} ∧
    ¬IsCupSet chi {0, 2, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1093 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1094 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 9} ∧
    ¬IsCupSet chi {0, 2, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1095 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 10} ∧
    ¬IsCupSet chi {0, 2, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1096 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1097 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1098 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 6} ∧
    ¬IsCupSet chi {0, 3, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1099 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 7} ∧
    ¬IsCupSet chi {0, 3, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1100 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 8} ∧
    ¬IsCupSet chi {0, 3, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1101 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 9} ∧
    ¬IsCupSet chi {0, 3, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1102 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 10} ∧
    ¬IsCupSet chi {0, 3, 4, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1103 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 7} ∧
    ¬IsCupSet chi {0, 3, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1104 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 8} ∧
    ¬IsCupSet chi {0, 3, 4, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1105 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 9} ∧
    ¬IsCupSet chi {0, 3, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1106 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 10} ∧
    ¬IsCupSet chi {0, 3, 4, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1107 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 8} ∧
    ¬IsCupSet chi {0, 3, 4, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1108 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 9} ∧
    ¬IsCupSet chi {0, 3, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1109 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 10} ∧
    ¬IsCupSet chi {0, 3, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1110 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 9} ∧
    ¬IsCupSet chi {0, 3, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1111 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 10} ∧
    ¬IsCupSet chi {0, 3, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1112 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 10} ∧
    ¬IsCupSet chi {0, 3, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1113 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 7} ∧
    ¬IsCupSet chi {0, 3, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1114 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 8} ∧
    ¬IsCupSet chi {0, 3, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1115 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 9} ∧
    ¬IsCupSet chi {0, 3, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1116 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 10} ∧
    ¬IsCupSet chi {0, 3, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1117 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 8} ∧
    ¬IsCupSet chi {0, 3, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1118 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 9} ∧
    ¬IsCupSet chi {0, 3, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1119 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 10} ∧
    ¬IsCupSet chi {0, 3, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1120 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 9} ∧
    ¬IsCupSet chi {0, 3, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1121 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 10} ∧
    ¬IsCupSet chi {0, 3, 5, 8, 10}

end ErdosSzekeres

end
