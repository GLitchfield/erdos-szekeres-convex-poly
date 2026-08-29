module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 017. -/

def SynchronizedFiveFanFin11OriginalAtom1004 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 9} ∧
    ¬IsCupSet chi {0, 1, 3, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1005 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1006 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1007 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 6} ∧
    ¬IsCupSet chi {0, 1, 4, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1008 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 7} ∧
    ¬IsCupSet chi {0, 1, 4, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1009 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 8} ∧
    ¬IsCupSet chi {0, 1, 4, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1010 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 9} ∧
    ¬IsCupSet chi {0, 1, 4, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1011 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 10} ∧
    ¬IsCupSet chi {0, 1, 4, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1012 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 7} ∧
    ¬IsCupSet chi {0, 1, 4, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1013 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 8} ∧
    ¬IsCupSet chi {0, 1, 4, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1014 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 9} ∧
    ¬IsCupSet chi {0, 1, 4, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1015 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 10} ∧
    ¬IsCupSet chi {0, 1, 4, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1016 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 8} ∧
    ¬IsCupSet chi {0, 1, 4, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1017 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 9} ∧
    ¬IsCupSet chi {0, 1, 4, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1018 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 10} ∧
    ¬IsCupSet chi {0, 1, 4, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1019 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 9} ∧
    ¬IsCupSet chi {0, 1, 4, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1020 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 10} ∧
    ¬IsCupSet chi {0, 1, 4, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1021 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 4, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1022 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 7} ∧
    ¬IsCupSet chi {0, 1, 5, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1023 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 8} ∧
    ¬IsCupSet chi {0, 1, 5, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1024 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 9} ∧
    ¬IsCupSet chi {0, 1, 5, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1025 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 10} ∧
    ¬IsCupSet chi {0, 1, 5, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1026 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 8} ∧
    ¬IsCupSet chi {0, 1, 5, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1027 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 9} ∧
    ¬IsCupSet chi {0, 1, 5, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1028 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 10} ∧
    ¬IsCupSet chi {0, 1, 5, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1029 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 9} ∧
    ¬IsCupSet chi {0, 1, 5, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1030 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 10} ∧
    ¬IsCupSet chi {0, 1, 5, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1031 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 5, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1032 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 8} ∧
    ¬IsCupSet chi {0, 1, 6, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1033 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 9} ∧
    ¬IsCupSet chi {0, 1, 6, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1034 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 10} ∧
    ¬IsCupSet chi {0, 1, 6, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1035 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 9} ∧
    ¬IsCupSet chi {0, 1, 6, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1036 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 10} ∧
    ¬IsCupSet chi {0, 1, 6, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1037 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 6, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1038 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 8, 9} ∧
    ¬IsCupSet chi {0, 1, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1039 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 8, 10} ∧
    ¬IsCupSet chi {0, 1, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1040 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1041 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom1042 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 5} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 5}

def SynchronizedFiveFanFin11OriginalAtom1043 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 6} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 6}

def SynchronizedFiveFanFin11OriginalAtom1044 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 7} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 7}

def SynchronizedFiveFanFin11OriginalAtom1045 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 8} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 8}

def SynchronizedFiveFanFin11OriginalAtom1046 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 9} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 9}

def SynchronizedFiveFanFin11OriginalAtom1047 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 10}

def SynchronizedFiveFanFin11OriginalAtom1048 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 6} ∧
    ¬IsCupSet chi {0, 2, 3, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom1049 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 7} ∧
    ¬IsCupSet chi {0, 2, 3, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom1050 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 8} ∧
    ¬IsCupSet chi {0, 2, 3, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom1051 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 9} ∧
    ¬IsCupSet chi {0, 2, 3, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom1052 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom1053 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 7} ∧
    ¬IsCupSet chi {0, 2, 3, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom1054 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 8} ∧
    ¬IsCupSet chi {0, 2, 3, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom1055 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 9} ∧
    ¬IsCupSet chi {0, 2, 3, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1056 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1057 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 8} ∧
    ¬IsCupSet chi {0, 2, 3, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1058 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 9} ∧
    ¬IsCupSet chi {0, 2, 3, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1059 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom1060 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 9} ∧
    ¬IsCupSet chi {0, 2, 3, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom1061 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom1062 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 9, 10}

end ErdosSzekeres

end
