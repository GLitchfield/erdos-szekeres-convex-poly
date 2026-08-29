module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Stable original semantic atoms, segment 016. -/

def SynchronizedFiveFanFin11OriginalAtom0945 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom0946 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom0947 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom0948 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom0949 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom0950 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom0951 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom0952 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom0953 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom0954 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom0955 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom0956 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom0957 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom0958 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 4} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 4}

def SynchronizedFiveFanFin11OriginalAtom0959 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 5} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 5}

def SynchronizedFiveFanFin11OriginalAtom0960 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 6} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 6}

def SynchronizedFiveFanFin11OriginalAtom0961 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 7} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 7}

def SynchronizedFiveFanFin11OriginalAtom0962 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 8} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 8}

def SynchronizedFiveFanFin11OriginalAtom0963 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 9}

def SynchronizedFiveFanFin11OriginalAtom0964 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 10}

def SynchronizedFiveFanFin11OriginalAtom0965 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 5} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 5}

def SynchronizedFiveFanFin11OriginalAtom0966 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 6} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 6}

def SynchronizedFiveFanFin11OriginalAtom0967 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 7} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 7}

def SynchronizedFiveFanFin11OriginalAtom0968 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 8} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 8}

def SynchronizedFiveFanFin11OriginalAtom0969 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 9}

def SynchronizedFiveFanFin11OriginalAtom0970 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 10}

def SynchronizedFiveFanFin11OriginalAtom0971 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 6} ∧
    ¬IsCupSet chi {0, 1, 2, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom0972 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 7} ∧
    ¬IsCupSet chi {0, 1, 2, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom0973 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 8} ∧
    ¬IsCupSet chi {0, 1, 2, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom0974 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom0975 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom0976 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 7} ∧
    ¬IsCupSet chi {0, 1, 2, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom0977 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 8} ∧
    ¬IsCupSet chi {0, 1, 2, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom0978 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom0979 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom0980 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 8} ∧
    ¬IsCupSet chi {0, 1, 2, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom0981 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom0982 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 7, 10}

def SynchronizedFiveFanFin11OriginalAtom0983 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 8, 9}

def SynchronizedFiveFanFin11OriginalAtom0984 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 8, 10}

def SynchronizedFiveFanFin11OriginalAtom0985 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 9, 10}

def SynchronizedFiveFanFin11OriginalAtom0986 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 5} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 5}

def SynchronizedFiveFanFin11OriginalAtom0987 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 6} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 6}

def SynchronizedFiveFanFin11OriginalAtom0988 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 7} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 7}

def SynchronizedFiveFanFin11OriginalAtom0989 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 8} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 8}

def SynchronizedFiveFanFin11OriginalAtom0990 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 9} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 9}

def SynchronizedFiveFanFin11OriginalAtom0991 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 10}

def SynchronizedFiveFanFin11OriginalAtom0992 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 6} ∧
    ¬IsCupSet chi {0, 1, 3, 5, 6}

def SynchronizedFiveFanFin11OriginalAtom0993 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 7} ∧
    ¬IsCupSet chi {0, 1, 3, 5, 7}

def SynchronizedFiveFanFin11OriginalAtom0994 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 8} ∧
    ¬IsCupSet chi {0, 1, 3, 5, 8}

def SynchronizedFiveFanFin11OriginalAtom0995 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 9} ∧
    ¬IsCupSet chi {0, 1, 3, 5, 9}

def SynchronizedFiveFanFin11OriginalAtom0996 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 5, 10}

def SynchronizedFiveFanFin11OriginalAtom0997 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 7} ∧
    ¬IsCupSet chi {0, 1, 3, 6, 7}

def SynchronizedFiveFanFin11OriginalAtom0998 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 8} ∧
    ¬IsCupSet chi {0, 1, 3, 6, 8}

def SynchronizedFiveFanFin11OriginalAtom0999 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 9} ∧
    ¬IsCupSet chi {0, 1, 3, 6, 9}

def SynchronizedFiveFanFin11OriginalAtom1000 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 6, 10}

def SynchronizedFiveFanFin11OriginalAtom1001 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 8} ∧
    ¬IsCupSet chi {0, 1, 3, 7, 8}

def SynchronizedFiveFanFin11OriginalAtom1002 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 9} ∧
    ¬IsCupSet chi {0, 1, 3, 7, 9}

def SynchronizedFiveFanFin11OriginalAtom1003 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 7, 10}

end ErdosSzekeres

end
