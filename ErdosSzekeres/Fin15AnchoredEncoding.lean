module

public import ErdosSzekeres.AnchoredPresentation
public import ErdosSzekeres.SynchronizedFiveFanFin11WindowTransport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-- The exact Fin15 support conclusion certified by the LRAT core. -/
def Fin15AnchoredConclusion (chi : TripleColoring 15) : Prop :=
  ∃ support : Finset (Fin 15),
    support.card = 8 ∧
    ¬ContainsStrongPolygonSet chi support 5

/-- The two equalities contributed by one ordered quadruple to the
strong-polygon predicate. -/
def Fin15AnchoredStrongQuad (chi : TripleColoring 15)
    (a b c d : Fin 15) (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=
  chi ⟨a, b, c, hab, hbc⟩ = chi ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
    chi ⟨a, c, d, hab.trans hbc, hcd⟩ = chi ⟨b, c, d, hbc, hcd⟩

def Fin15AnchoredAtom0001 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0002 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0003 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0004 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0005 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0006 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0007 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0008 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0009 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0010 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0011 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0012 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0013 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 1, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0014 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0015 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0016 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0017 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0018 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0019 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0020 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0021 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0022 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0023 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0024 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0025 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 2, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0026 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0027 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0028 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0029 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0030 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0031 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0032 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0033 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 3, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0034 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0035 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 3, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0036 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 3, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0037 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0038 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0039 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0040 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0041 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0042 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0043 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 4, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0044 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0045 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 4, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0046 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 4, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0047 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0048 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0049 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0050 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0051 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0052 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 5, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0053 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0054 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 5, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0055 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 5, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0056 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0057 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0058 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0059 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0060 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 6, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0061 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0062 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 6, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0063 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 6, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0064 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0065 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0066 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0067 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 7, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0068 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0069 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 7, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0070 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 7, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0071 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0072 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0074 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0075 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 8, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0076 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 8, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0077 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0078 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 9, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0079 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0080 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 9, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0081 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 9, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0082 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 10, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0083 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0084 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 10, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0085 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 10, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0086 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 11, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0087 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 11, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0088 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 11, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0089 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0090 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0091 (chi : TripleColoring 15) : Prop :=
  chi ⟨0, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0092 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0093 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0094 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0095 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0096 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0097 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0098 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0099 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0100 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0101 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0102 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0103 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0104 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0105 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0106 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0107 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0108 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0109 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0110 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0111 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0112 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0113 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0114 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0115 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0116 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0117 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0118 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0119 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0120 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0121 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0122 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0123 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0124 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0125 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0126 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0127 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0128 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0129 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0130 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0131 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0132 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0133 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0134 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0135 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0136 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0137 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0138 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0139 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0140 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0141 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0142 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0143 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0144 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0145 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0146 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0147 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0148 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0149 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0150 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0152 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0153 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0154 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0155 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0156 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0157 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0158 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0159 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0160 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0161 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0162 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0163 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0164 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0165 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0166 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0167 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0168 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0169 (chi : TripleColoring 15) : Prop :=
  chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0170 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0171 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0172 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0173 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0174 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0175 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0176 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0177 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0178 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0179 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0180 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0181 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0182 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0183 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0184 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0185 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0186 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0187 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0188 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0189 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0190 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0191 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0192 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0193 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0194 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0195 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0196 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0197 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0198 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0199 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0200 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0201 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0202 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0203 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0204 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0205 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0206 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0207 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0208 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0209 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0210 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0211 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0212 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0213 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0214 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0215 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0216 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0218 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0219 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0220 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0221 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0222 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0223 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0224 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0225 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0226 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0227 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0228 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0229 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0230 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0231 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0232 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0233 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0234 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0235 (chi : TripleColoring 15) : Prop :=
  chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0236 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0237 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0238 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0239 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0240 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0241 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0242 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0243 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0244 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0245 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0246 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0247 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0248 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0249 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0250 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0251 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0252 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0253 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0254 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0255 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0256 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0257 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0258 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0259 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0260 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0261 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0262 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0263 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0264 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0265 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0266 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0267 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0268 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0269 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0270 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0271 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0273 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0274 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0275 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0276 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0277 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0278 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0279 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0280 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0281 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0282 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0283 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0284 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0285 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0286 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 11, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0287 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 11, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0288 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0289 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0290 (chi : TripleColoring 15) : Prop :=
  chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0291 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0292 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0293 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0294 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0295 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0296 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0297 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0298 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0299 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0300 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0301 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0302 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0303 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0304 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0305 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0306 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0307 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0308 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0309 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0310 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0311 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0312 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0313 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0314 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0315 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0316 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0318 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0319 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0320 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0321 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0322 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0323 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0324 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0325 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0326 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0327 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0328 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 10, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0329 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 10, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0330 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0331 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0332 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0333 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0334 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0335 (chi : TripleColoring 15) : Prop :=
  chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0336 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0337 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0338 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0339 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0340 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0341 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0342 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0343 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0344 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0345 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0346 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0347 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0348 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0349 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0350 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0351 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0352 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0354 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0355 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0356 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0357 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0358 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0359 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0360 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0361 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0362 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0363 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0364 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 10, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0365 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 10, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0366 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0367 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0368 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0369 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0370 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0371 (chi : TripleColoring 15) : Prop :=
  chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0372 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0373 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0374 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0375 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0376 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0377 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0378 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0379 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0380 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0382 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0383 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0384 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0385 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0386 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0387 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0388 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0389 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0390 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0391 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0392 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0393 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0394 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0395 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0396 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0397 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0398 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0399 (chi : TripleColoring 15) : Prop :=
  chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0400 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0401 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0403 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0404 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0405 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0406 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0407 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0408 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0409 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0410 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0411 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0412 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0413 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0414 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0415 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0416 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0417 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0418 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0419 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0420 (chi : TripleColoring 15) : Prop :=
  chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0421 (chi : TripleColoring 15) : Prop :=
  chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0423 (chi : TripleColoring 15) : Prop :=
  chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0424 (chi : TripleColoring 15) : Prop :=
  chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0425 (chi : TripleColoring 15) : Prop :=
  chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0427 (chi : TripleColoring 15) : Prop :=
  chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0428 (chi : TripleColoring 15) : Prop :=
  chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0429 (chi : TripleColoring 15) : Prop :=
  chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0433 (chi : TripleColoring 15) : Prop :=
  chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0434 (chi : TripleColoring 15) : Prop :=
  chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0435 (chi : TripleColoring 15) : Prop :=
  chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0436 (chi : TripleColoring 15) : Prop :=
  chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0437 (chi : TripleColoring 15) : Prop :=
  chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0438 (chi : TripleColoring 15) : Prop :=
  chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0439 (chi : TripleColoring 15) : Prop :=
  chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0440 (chi : TripleColoring 15) : Prop :=
  chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0441 (chi : TripleColoring 15) : Prop :=
  chi ⟨9, 11, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0442 (chi : TripleColoring 15) : Prop :=
  chi ⟨9, 11, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0443 (chi : TripleColoring 15) : Prop :=
  chi ⟨9, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0444 (chi : TripleColoring 15) : Prop :=
  chi ⟨9, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0445 (chi : TripleColoring 15) : Prop :=
  chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0446 (chi : TripleColoring 15) : Prop :=
  chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0447 (chi : TripleColoring 15) : Prop :=
  chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0448 (chi : TripleColoring 15) : Prop :=
  chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0449 (chi : TripleColoring 15) : Prop :=
  chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0450 (chi : TripleColoring 15) : Prop :=
  chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0451 (chi : TripleColoring 15) : Prop :=
  chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0452 (chi : TripleColoring 15) : Prop :=
  chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0453 (chi : TripleColoring 15) : Prop :=
  chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0454 (chi : TripleColoring 15) : Prop :=
  chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0455 (chi : TripleColoring 15) : Prop :=
  chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left

def Fin15AnchoredAtom0456 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 3 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0457 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 4 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0458 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 5 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0459 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0460 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0461 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0462 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0463 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0464 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0465 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0466 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0467 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 2 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0468 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 3 4 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0469 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 3 5 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0470 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 3 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0471 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 3 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0472 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 3 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0473 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 3 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0474 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 3 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0475 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 3 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0476 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 3 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0477 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 3 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0478 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 3 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0479 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 4 5 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0480 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 4 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0481 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 4 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0482 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 4 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0483 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 4 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0484 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 4 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0485 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 4 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0486 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 4 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0487 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 4 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0488 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 4 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0489 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 5 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0490 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 5 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0491 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 5 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0492 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 5 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0493 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 5 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0494 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 5 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0495 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 5 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0496 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 5 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0497 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 5 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0498 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0499 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0500 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0501 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0502 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0503 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0504 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0505 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0506 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0507 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0508 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0509 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0510 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0511 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0512 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0513 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0514 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0516 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0517 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0518 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0519 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0520 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0521 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0522 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0523 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0524 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0525 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0526 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0527 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0528 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0529 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0530 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0531 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0532 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0533 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 1 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0534 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 3 4 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0535 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0536 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0537 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0538 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 3 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0539 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0540 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 3 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0541 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 3 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0542 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 3 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0543 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 3 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0544 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 3 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0545 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 4 5 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0546 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 4 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0547 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 4 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0548 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 4 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0549 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 4 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0550 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 4 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0551 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 4 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0552 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 4 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0553 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 4 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0554 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 4 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0555 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 5 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0556 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 5 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0557 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 5 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0558 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 5 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0559 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 5 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0560 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 5 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0561 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 5 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0562 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 5 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0563 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 5 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0564 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0565 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0566 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0567 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0568 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0569 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0570 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0571 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0572 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0573 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0574 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0575 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0576 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0577 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0578 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0579 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0580 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0582 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0583 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0584 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0585 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0586 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0587 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0588 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0589 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0590 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0591 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0592 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0593 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0594 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0595 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0596 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0597 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0598 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0599 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 2 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0600 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0601 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0602 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0603 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 4 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0604 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0605 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0606 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 4 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0607 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 4 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0608 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 4 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0609 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 4 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0610 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 5 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0611 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 5 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0612 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 5 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0613 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 5 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0614 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 5 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0615 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 5 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0616 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 5 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0617 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 5 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0618 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 5 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0619 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0620 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0621 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0622 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0623 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0624 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0625 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0626 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0627 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0628 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0629 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0630 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0631 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0632 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0633 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0634 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0635 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0637 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0638 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0639 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0640 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0641 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0642 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0643 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0644 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0645 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0646 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0647 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0648 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0649 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0650 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0651 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0652 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0653 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0654 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 3 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0655 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 5 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0656 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 5 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0657 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 5 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0658 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 5 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0659 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 5 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0660 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 5 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0661 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 5 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0662 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 5 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0663 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 5 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0664 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0665 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0666 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0667 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0668 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0669 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0670 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0671 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0672 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0673 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0674 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0675 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0676 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0677 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0678 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0679 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0680 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0682 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0683 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0684 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0685 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0686 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0687 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0688 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0689 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0690 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0691 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0692 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0693 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0694 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0695 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0696 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0697 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0698 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0699 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 4 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0700 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0701 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0702 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0703 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0704 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0705 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0706 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0707 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0708 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0709 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0710 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0711 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0712 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0713 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0714 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0715 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0716 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0718 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0719 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0720 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0721 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0722 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0723 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0724 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0725 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0726 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0727 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0728 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0729 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0730 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0731 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0732 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0733 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0734 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0735 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 5 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0736 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0737 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0738 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0739 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0740 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0741 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0742 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0743 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0744 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0746 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0747 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0748 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0749 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0750 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0751 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0752 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0753 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0754 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0755 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0756 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0757 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0758 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0759 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0760 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0761 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0762 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0763 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 6 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0764 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0765 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0767 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0768 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0769 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0770 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0771 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0772 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0773 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0774 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0775 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0776 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0777 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0778 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0779 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0780 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0781 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0782 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0783 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0784 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 7 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0785 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 8 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0787 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 8 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0788 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 8 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0789 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 8 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0791 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 8 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0792 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 8 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0793 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 8 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0797 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 8 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0798 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 8 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0799 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 8 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0800 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 9 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0801 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 9 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0802 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 9 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0803 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 9 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0804 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 9 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0805 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 9 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0806 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 9 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0807 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 9 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0808 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 9 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0809 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 9 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0810 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 10 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0811 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 10 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0812 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 10 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0813 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 10 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0814 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 10 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0815 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 10 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0816 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 11 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0817 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 11 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0818 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 11 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0819 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 0 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0820 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 3 4 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0821 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 3 5 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0822 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 3 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0823 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 3 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0824 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 3 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0825 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 3 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0826 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 3 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0827 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 3 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0828 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 3 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0829 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 3 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0830 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 3 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0831 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 4 5 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0832 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 4 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0833 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 4 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0834 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 4 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0835 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 4 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0836 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 4 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0837 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 4 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0838 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 4 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0839 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 4 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0840 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 4 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0841 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 5 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0842 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 5 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0843 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 5 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0844 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 5 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0845 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 5 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0846 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 5 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0847 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 5 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0848 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 5 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0849 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 5 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0850 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0851 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0852 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0853 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0854 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0855 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0856 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0857 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0858 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0859 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0860 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0861 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0862 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0863 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0864 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0865 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0866 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0868 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0870 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0871 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0872 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0873 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0874 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0875 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0876 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0877 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0878 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0879 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0880 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0881 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0882 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0883 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0884 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0885 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 2 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0886 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 4 5 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0887 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 4 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0888 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 4 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0889 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 4 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0890 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 4 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0891 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 4 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0892 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 4 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0893 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 4 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0894 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 4 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0895 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 4 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0896 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 5 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0897 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 5 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0898 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 5 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0899 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 5 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0900 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 5 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0901 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 5 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0902 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 5 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0903 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 5 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0904 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 5 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0905 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0906 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0907 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0908 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0909 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0910 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0911 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0912 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0913 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0914 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0915 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0916 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0917 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0918 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0919 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0920 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0921 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0923 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0924 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0925 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0926 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0927 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0928 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0929 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0930 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0931 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0932 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0933 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0934 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0935 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0936 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0937 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0938 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0939 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0940 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 3 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0941 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 5 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0942 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 5 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0943 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 5 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0944 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 5 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0945 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 5 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0946 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 5 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0947 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 5 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0948 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 5 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0949 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 5 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0950 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0951 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0952 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0953 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0954 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0955 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0956 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0957 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0958 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0959 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0960 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0961 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0962 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0963 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0964 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0965 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0966 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0968 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0969 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0970 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0971 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0972 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0973 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0974 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0975 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0976 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0977 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0978 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0979 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0980 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0981 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0982 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0983 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0984 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0985 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 4 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0986 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0987 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0988 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0989 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0990 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0991 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0992 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0993 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0994 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0995 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0996 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0997 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0998 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom0999 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1000 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1001 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1002 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1004 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1005 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1006 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1007 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1008 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1009 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1010 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1011 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1012 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1013 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1014 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1015 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1016 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1017 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1019 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1020 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1021 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 5 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1022 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1023 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1024 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1025 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1026 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1027 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1028 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1029 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1030 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1032 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1033 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1034 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1035 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1036 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1037 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1038 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1039 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1040 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1041 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1042 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1043 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1044 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1046 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1047 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1048 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1049 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 6 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1050 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1051 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1053 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1054 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1055 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1056 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1057 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1058 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1059 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1060 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1061 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1062 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1063 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1064 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1065 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1066 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1067 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1068 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1069 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1070 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 7 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1071 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 8 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1073 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 8 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1074 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 8 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1075 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 8 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1077 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 8 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1078 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 8 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1079 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 8 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1083 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 8 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1084 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 8 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1085 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 8 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1086 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 9 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1087 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 9 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1088 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 9 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1089 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 9 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1090 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 9 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1091 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 9 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1092 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 9 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1093 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 9 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1094 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 9 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1095 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 9 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1096 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 10 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1097 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 10 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1098 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 10 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1099 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 10 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1100 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 10 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1101 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 10 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1102 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 11 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1103 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 11 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1104 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 11 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1105 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 1 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1106 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 4 5 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1107 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 4 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1108 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 4 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1109 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 4 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1110 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 4 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1111 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 4 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1112 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 4 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1113 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 4 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1114 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 4 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1115 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 4 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1116 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 5 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1117 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 5 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1118 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 5 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1119 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 5 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1120 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 5 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1121 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 5 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1122 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 5 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1123 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 5 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1124 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 5 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1125 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1126 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1127 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1128 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1129 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1130 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1131 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1132 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1133 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1134 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1135 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1136 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1137 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1138 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1139 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1140 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1141 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1143 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1144 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1145 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1146 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1147 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1148 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1149 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1150 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1151 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1152 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1153 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1154 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1155 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1156 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1157 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1158 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1159 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1160 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 3 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1161 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 5 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1162 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 5 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1163 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 5 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1164 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 5 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1165 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 5 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1166 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 5 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1167 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 5 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1168 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 5 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1169 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 5 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1170 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1171 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1172 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1173 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1174 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1175 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1176 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1177 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1178 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1179 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1180 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1181 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1182 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1183 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1184 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1185 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1186 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1188 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1189 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1190 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1191 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1192 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1193 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1194 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1195 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1196 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1197 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1198 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1199 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1200 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1201 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1203 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1204 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1205 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 4 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1206 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1207 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1208 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1209 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1210 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1211 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1212 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1213 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1214 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1215 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1216 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1217 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1218 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1219 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1220 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1221 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1222 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1226 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1227 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1228 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1229 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1230 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1231 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1232 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1233 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1234 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1235 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1236 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1237 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1238 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1239 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1240 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1241 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 5 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1242 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1243 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1244 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1245 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1246 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1247 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1248 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1249 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1250 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1252 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1253 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1255 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1256 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1257 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1258 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1259 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1260 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1261 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1262 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1263 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1264 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1265 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1266 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1267 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1268 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1269 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 6 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1270 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1271 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1273 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1274 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1275 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1276 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1277 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1278 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1279 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1280 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1281 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1282 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1283 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1284 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1285 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1286 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1287 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1288 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1289 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1290 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 7 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1291 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 8 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1293 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 8 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1297 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 8 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1298 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 8 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1303 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 8 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1304 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 8 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1305 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 8 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1306 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 9 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1307 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 9 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1308 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 9 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1309 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 9 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1310 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 9 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1311 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 9 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1312 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 9 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1313 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 9 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1314 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 9 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1315 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 9 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1316 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 10 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1317 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 10 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1318 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 10 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1319 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 10 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1320 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 10 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1321 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 10 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1322 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 11 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1323 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 11 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1324 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 11 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1325 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 2 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1326 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 5 6 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1327 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 5 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1328 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 5 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1329 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 5 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1330 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 5 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1331 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 5 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1332 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 5 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1333 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 5 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1334 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 5 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1335 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1336 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1337 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1338 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1339 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1340 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1341 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1342 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1343 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1344 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1345 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1346 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1347 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1348 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1349 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1350 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1351 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1353 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1354 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1355 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1356 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1357 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1358 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1359 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1360 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1361 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1362 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1363 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1364 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1365 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1366 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1367 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1368 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1369 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1370 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 4 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1371 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1372 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1373 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1374 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1375 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1376 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1377 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1378 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1379 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1380 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1381 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1382 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1383 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1384 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1385 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1386 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1387 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1389 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1390 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1391 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1392 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1393 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1394 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1395 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1396 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1397 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1398 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1399 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1400 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1401 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1402 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1403 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1404 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1405 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1406 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 5 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1407 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1408 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1409 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1410 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1411 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1412 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1413 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1414 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1415 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1417 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1418 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1419 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1420 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1421 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1422 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1423 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1424 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1425 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1426 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1427 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1428 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1429 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1430 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1432 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1433 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1434 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 6 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1435 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1436 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1438 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1439 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1440 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1441 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1442 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1443 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1444 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1445 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1446 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1447 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1448 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1449 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1450 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1452 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1453 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1454 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1455 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 7 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1456 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 8 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1458 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 8 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1459 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 8 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1460 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 8 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1462 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 8 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1463 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 8 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1464 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 8 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1468 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 8 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1469 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 8 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1470 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 8 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1471 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 9 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1472 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 9 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1473 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 9 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1474 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 9 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1475 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 9 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1476 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 9 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1477 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 9 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1478 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 9 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1479 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 9 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1480 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 9 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1481 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 10 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1482 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 10 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1483 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 10 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1484 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 10 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1485 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 10 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1486 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 10 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1487 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 11 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1488 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 11 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1489 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 11 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1490 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 3 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1491 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 6 7 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1492 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 6 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1493 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 6 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1494 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 6 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1495 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 6 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1496 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 6 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1497 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 6 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1498 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 6 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1499 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1500 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1501 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1502 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1503 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1504 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1505 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1506 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1507 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1509 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1510 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1511 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1512 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1513 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1514 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1515 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1516 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1517 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1518 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1519 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1520 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1521 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1522 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1523 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1524 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1525 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1526 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 5 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1527 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1528 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1529 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1530 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1531 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1532 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1533 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1534 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1535 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1537 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1538 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1539 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1540 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1541 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1542 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1543 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1544 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1545 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1546 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1547 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1548 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1549 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1550 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1551 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1552 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1553 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1554 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 6 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1555 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1556 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1558 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1559 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1560 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1561 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1562 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1563 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1564 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1565 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1566 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1567 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1568 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1569 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1570 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1571 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1572 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1573 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1574 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1575 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 7 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1576 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 8 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1578 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 8 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1579 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 8 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1580 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 8 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1582 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 8 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1583 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 8 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1584 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 8 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1588 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 8 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1589 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 8 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1590 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 8 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1591 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 9 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1592 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 9 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1593 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 9 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1594 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 9 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1595 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 9 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1596 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 9 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1597 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 9 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1598 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 9 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1599 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 9 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1600 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 9 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1601 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 10 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1602 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 10 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1603 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 10 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1604 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 10 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1605 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 10 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1606 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 10 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1607 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 11 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1608 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 11 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1610 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 4 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1611 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 7 8 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1612 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 7 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1613 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 7 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1614 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 7 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1615 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 7 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1616 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 7 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1617 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 7 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1618 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1619 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1621 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1622 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1623 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1624 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1625 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1626 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1627 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1628 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1629 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1630 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1631 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1632 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1633 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1634 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1635 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1636 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1637 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1638 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 6 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1639 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1640 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1642 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1643 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1644 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1645 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1646 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1647 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1648 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1649 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1650 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1651 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1652 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1653 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1654 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1655 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1656 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1657 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1658 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1659 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 7 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1660 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 8 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1662 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 8 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1663 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 8 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1664 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 8 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1666 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 8 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1667 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 8 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1668 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 8 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1672 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 8 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1673 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 8 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1674 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 8 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1675 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 9 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1676 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 9 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1677 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 9 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1678 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 9 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1679 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 9 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1680 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 9 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1681 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 9 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1682 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 9 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1683 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 9 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1684 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 9 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1685 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 10 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1686 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 10 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1687 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 10 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1688 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 10 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1689 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 10 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1690 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 10 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1691 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 11 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1692 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 11 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1693 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 11 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1694 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 5 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1695 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 8 9 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1696 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 8 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1698 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 8 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1699 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 8 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1700 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 8 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1701 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1702 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 9 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1703 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1704 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1705 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1706 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1707 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1708 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1709 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1710 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1711 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1712 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1713 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1714 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1715 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 7 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1716 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 8 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1718 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 8 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1719 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 8 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1720 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 8 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1722 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 8 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1723 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 8 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1724 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 8 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1728 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 8 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1729 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 8 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1730 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 8 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1731 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 9 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1732 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 9 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1733 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 9 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1734 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 9 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1735 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 9 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1736 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 9 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1737 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 9 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1738 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 9 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1739 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 9 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1740 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 9 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1741 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 10 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1742 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 10 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1743 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 10 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1744 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 10 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1745 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 10 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1746 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 10 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1747 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 11 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1748 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 11 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1750 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 6 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1751 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 8 9 10 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1753 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 8 9 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1754 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 8 9 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1755 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 8 9 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1757 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 8 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1758 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 8 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1759 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 8 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1763 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 8 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1764 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 8 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1765 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 8 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1766 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 9 10 11 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1767 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 9 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1768 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 9 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1769 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 9 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1770 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 9 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1771 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 9 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1772 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 9 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1773 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 9 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1774 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 9 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1775 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 9 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1776 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 10 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1777 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 10 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1778 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 10 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1779 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 10 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1780 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 10 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1781 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 10 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1782 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 11 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1783 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 11 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1784 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 11 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1785 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 7 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1787 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 8 9 10 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1788 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 8 9 10 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1789 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 8 9 10 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1793 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 8 9 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1794 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 8 9 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1795 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 8 9 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1799 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 8 10 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1800 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 8 10 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1801 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 8 10 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1805 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 8 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1806 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 9 10 11 12 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1807 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 9 10 11 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1808 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 9 10 11 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1809 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 9 10 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1810 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 9 10 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1811 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 9 10 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1812 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 9 11 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1813 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 9 11 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1814 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 9 11 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1815 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 9 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1816 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 10 11 12 13 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1817 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 10 11 12 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1818 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 10 11 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1819 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 10 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1820 (chi : TripleColoring 15) : Prop :=
  Fin15AnchoredStrongQuad chi 11 12 13 14 (by decide) (by decide) (by decide)

def Fin15AnchoredAtom1821 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 4}

def Fin15AnchoredAtom1822 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 5}

def Fin15AnchoredAtom1823 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 6}

def Fin15AnchoredAtom1824 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 7}

def Fin15AnchoredAtom1825 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 8}

def Fin15AnchoredAtom1826 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 9}

def Fin15AnchoredAtom1827 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 10}

def Fin15AnchoredAtom1828 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 11}

def Fin15AnchoredAtom1829 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 12}

def Fin15AnchoredAtom1830 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 13}

def Fin15AnchoredAtom1831 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 14}

def Fin15AnchoredAtom1832 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 5}

def Fin15AnchoredAtom1833 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 6}

def Fin15AnchoredAtom1834 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 7}

def Fin15AnchoredAtom1835 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 8}

def Fin15AnchoredAtom1836 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 9}

def Fin15AnchoredAtom1837 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 10}

def Fin15AnchoredAtom1838 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 11}

def Fin15AnchoredAtom1839 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 12}

def Fin15AnchoredAtom1840 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 13}

def Fin15AnchoredAtom1841 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 14}

def Fin15AnchoredAtom1842 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 6}

def Fin15AnchoredAtom1843 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 7}

def Fin15AnchoredAtom1844 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 8}

def Fin15AnchoredAtom1845 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 9}

def Fin15AnchoredAtom1846 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 10}

def Fin15AnchoredAtom1847 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 11}

def Fin15AnchoredAtom1848 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 12}

def Fin15AnchoredAtom1849 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 13}

def Fin15AnchoredAtom1850 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 14}

def Fin15AnchoredAtom1851 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 7}

def Fin15AnchoredAtom1852 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 8}

def Fin15AnchoredAtom1853 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 9}

def Fin15AnchoredAtom1854 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 10}

def Fin15AnchoredAtom1855 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 11}

def Fin15AnchoredAtom1856 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 12}

def Fin15AnchoredAtom1857 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 13}

def Fin15AnchoredAtom1858 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 14}

def Fin15AnchoredAtom1859 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 8}

def Fin15AnchoredAtom1860 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 9}

def Fin15AnchoredAtom1861 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 10}

def Fin15AnchoredAtom1862 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 11}

def Fin15AnchoredAtom1863 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 12}

def Fin15AnchoredAtom1864 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 13}

def Fin15AnchoredAtom1865 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 14}

def Fin15AnchoredAtom1866 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 9}

def Fin15AnchoredAtom1867 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 10}

def Fin15AnchoredAtom1869 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 12}

def Fin15AnchoredAtom1871 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 14}

def Fin15AnchoredAtom1872 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 9, 10}

def Fin15AnchoredAtom1873 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 9, 11}

def Fin15AnchoredAtom1874 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 9, 12}

def Fin15AnchoredAtom1875 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 9, 13}

def Fin15AnchoredAtom1876 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 9, 14}

def Fin15AnchoredAtom1877 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 10, 11}

def Fin15AnchoredAtom1878 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 10, 12}

def Fin15AnchoredAtom1879 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 10, 13}

def Fin15AnchoredAtom1880 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 10, 14}

def Fin15AnchoredAtom1881 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 11, 12}

def Fin15AnchoredAtom1882 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 11, 13}

def Fin15AnchoredAtom1883 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 11, 14}

def Fin15AnchoredAtom1884 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 12, 13}

def Fin15AnchoredAtom1885 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 12, 14}

def Fin15AnchoredAtom1886 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 13, 14}

def Fin15AnchoredAtom1887 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 5}

def Fin15AnchoredAtom1888 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 6}

def Fin15AnchoredAtom1889 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 7}

def Fin15AnchoredAtom1890 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 8}

def Fin15AnchoredAtom1891 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 9}

def Fin15AnchoredAtom1892 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 10}

def Fin15AnchoredAtom1893 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 11}

def Fin15AnchoredAtom1894 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 12}

def Fin15AnchoredAtom1895 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 13}

def Fin15AnchoredAtom1896 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 14}

def Fin15AnchoredAtom1897 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 6}

def Fin15AnchoredAtom1898 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 7}

def Fin15AnchoredAtom1899 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 8}

def Fin15AnchoredAtom1900 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 9}

def Fin15AnchoredAtom1901 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 10}

def Fin15AnchoredAtom1902 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 11}

def Fin15AnchoredAtom1903 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 12}

def Fin15AnchoredAtom1904 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 13}

def Fin15AnchoredAtom1905 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 14}

def Fin15AnchoredAtom1906 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 7}

def Fin15AnchoredAtom1907 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 8}

def Fin15AnchoredAtom1908 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 9}

def Fin15AnchoredAtom1909 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 10}

def Fin15AnchoredAtom1910 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 11}

def Fin15AnchoredAtom1911 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 12}

def Fin15AnchoredAtom1912 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 13}

def Fin15AnchoredAtom1913 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 14}

def Fin15AnchoredAtom1914 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 8}

def Fin15AnchoredAtom1915 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 9}

def Fin15AnchoredAtom1916 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 10}

def Fin15AnchoredAtom1917 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 11}

def Fin15AnchoredAtom1918 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 12}

def Fin15AnchoredAtom1919 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 13}

def Fin15AnchoredAtom1920 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 14}

def Fin15AnchoredAtom1921 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 9}

def Fin15AnchoredAtom1922 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 10}

def Fin15AnchoredAtom1924 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 12}

def Fin15AnchoredAtom1925 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 13}

def Fin15AnchoredAtom1926 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 14}

def Fin15AnchoredAtom1927 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 9, 10}

def Fin15AnchoredAtom1928 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 9, 11}

def Fin15AnchoredAtom1929 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 9, 12}

def Fin15AnchoredAtom1930 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 9, 13}

def Fin15AnchoredAtom1931 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 9, 14}

def Fin15AnchoredAtom1932 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 10, 11}

def Fin15AnchoredAtom1933 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 10, 12}

def Fin15AnchoredAtom1934 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 10, 13}

def Fin15AnchoredAtom1935 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 10, 14}

def Fin15AnchoredAtom1936 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 11, 12}

def Fin15AnchoredAtom1937 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 11, 13}

def Fin15AnchoredAtom1938 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 11, 14}

def Fin15AnchoredAtom1939 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 12, 13}

def Fin15AnchoredAtom1940 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 12, 14}

def Fin15AnchoredAtom1941 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 13, 14}

def Fin15AnchoredAtom1942 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 6}

def Fin15AnchoredAtom1943 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 7}

def Fin15AnchoredAtom1944 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 8}

def Fin15AnchoredAtom1945 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 9}

def Fin15AnchoredAtom1946 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 10}

def Fin15AnchoredAtom1947 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 11}

def Fin15AnchoredAtom1948 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 12}

def Fin15AnchoredAtom1949 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 13}

def Fin15AnchoredAtom1950 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 14}

def Fin15AnchoredAtom1951 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 7}

def Fin15AnchoredAtom1952 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 8}

def Fin15AnchoredAtom1953 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 9}

def Fin15AnchoredAtom1954 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 10}

def Fin15AnchoredAtom1955 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 11}

def Fin15AnchoredAtom1956 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 12}

def Fin15AnchoredAtom1957 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 13}

def Fin15AnchoredAtom1958 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 14}

def Fin15AnchoredAtom1959 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 8}

def Fin15AnchoredAtom1960 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 9}

def Fin15AnchoredAtom1961 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 10}

def Fin15AnchoredAtom1962 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 11}

def Fin15AnchoredAtom1963 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 12}

def Fin15AnchoredAtom1964 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 13}

def Fin15AnchoredAtom1965 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 14}

def Fin15AnchoredAtom1966 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 9}

def Fin15AnchoredAtom1967 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 10}

def Fin15AnchoredAtom1969 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 12}

def Fin15AnchoredAtom1970 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 13}

def Fin15AnchoredAtom1971 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 14}

def Fin15AnchoredAtom1972 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 9, 10}

def Fin15AnchoredAtom1973 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 9, 11}

def Fin15AnchoredAtom1974 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 9, 12}

def Fin15AnchoredAtom1975 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 9, 13}

def Fin15AnchoredAtom1976 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 9, 14}

def Fin15AnchoredAtom1977 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 10, 11}

def Fin15AnchoredAtom1978 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 10, 12}

def Fin15AnchoredAtom1979 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 10, 13}

def Fin15AnchoredAtom1980 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 10, 14}

def Fin15AnchoredAtom1981 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 11, 12}

def Fin15AnchoredAtom1982 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 11, 13}

def Fin15AnchoredAtom1983 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 11, 14}

def Fin15AnchoredAtom1984 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 12, 13}

def Fin15AnchoredAtom1985 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 12, 14}

def Fin15AnchoredAtom1986 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 13, 14}

def Fin15AnchoredAtom1987 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 7}

def Fin15AnchoredAtom1988 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 8}

def Fin15AnchoredAtom1989 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 9}

def Fin15AnchoredAtom1990 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 10}

def Fin15AnchoredAtom1991 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 11}

def Fin15AnchoredAtom1992 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 12}

def Fin15AnchoredAtom1993 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 13}

def Fin15AnchoredAtom1994 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 14}

def Fin15AnchoredAtom1995 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 8}

def Fin15AnchoredAtom1996 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 9}

def Fin15AnchoredAtom1997 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 10}

def Fin15AnchoredAtom1998 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 11}

def Fin15AnchoredAtom1999 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 12}

def Fin15AnchoredAtom2000 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 13}

def Fin15AnchoredAtom2001 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 14}

def Fin15AnchoredAtom2002 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 9}

def Fin15AnchoredAtom2003 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 10}

def Fin15AnchoredAtom2005 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 12}

def Fin15AnchoredAtom2006 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 13}

def Fin15AnchoredAtom2007 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 14}

def Fin15AnchoredAtom2008 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 9, 10}

def Fin15AnchoredAtom2009 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 9, 11}

def Fin15AnchoredAtom2010 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 9, 12}

def Fin15AnchoredAtom2011 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 9, 13}

def Fin15AnchoredAtom2012 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 9, 14}

def Fin15AnchoredAtom2013 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 10, 11}

def Fin15AnchoredAtom2014 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 10, 12}

def Fin15AnchoredAtom2015 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 10, 13}

def Fin15AnchoredAtom2016 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 10, 14}

def Fin15AnchoredAtom2017 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 11, 12}

def Fin15AnchoredAtom2018 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 11, 13}

def Fin15AnchoredAtom2019 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 11, 14}

def Fin15AnchoredAtom2020 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 12, 13}

def Fin15AnchoredAtom2021 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 12, 14}

def Fin15AnchoredAtom2022 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 13, 14}

def Fin15AnchoredAtom2023 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 8}

def Fin15AnchoredAtom2024 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 9}

def Fin15AnchoredAtom2025 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 10}

def Fin15AnchoredAtom2026 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 11}

def Fin15AnchoredAtom2027 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 12}

def Fin15AnchoredAtom2028 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 13}

def Fin15AnchoredAtom2029 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 14}

def Fin15AnchoredAtom2030 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 9}

def Fin15AnchoredAtom2031 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 10}

def Fin15AnchoredAtom2033 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 12}

def Fin15AnchoredAtom2034 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 13}

def Fin15AnchoredAtom2035 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 14}

def Fin15AnchoredAtom2036 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 9, 10}

def Fin15AnchoredAtom2037 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 9, 11}

def Fin15AnchoredAtom2038 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 9, 12}

def Fin15AnchoredAtom2039 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 9, 13}

def Fin15AnchoredAtom2040 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 9, 14}

def Fin15AnchoredAtom2041 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 10, 11}

def Fin15AnchoredAtom2042 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 10, 12}

def Fin15AnchoredAtom2043 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 10, 13}

def Fin15AnchoredAtom2044 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 10, 14}

def Fin15AnchoredAtom2045 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 11, 12}

def Fin15AnchoredAtom2046 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 11, 13}

def Fin15AnchoredAtom2047 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 11, 14}

def Fin15AnchoredAtom2048 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 12, 13}

def Fin15AnchoredAtom2049 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 12, 14}

def Fin15AnchoredAtom2050 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 13, 14}

def Fin15AnchoredAtom2051 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 8, 9}

def Fin15AnchoredAtom2052 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 8, 10}

def Fin15AnchoredAtom2054 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 8, 12}

def Fin15AnchoredAtom2055 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 8, 13}

def Fin15AnchoredAtom2056 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 8, 14}

def Fin15AnchoredAtom2057 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 9, 10}

def Fin15AnchoredAtom2058 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 9, 11}

def Fin15AnchoredAtom2059 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 9, 12}

def Fin15AnchoredAtom2060 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 9, 13}

def Fin15AnchoredAtom2061 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 9, 14}

def Fin15AnchoredAtom2062 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 10, 11}

def Fin15AnchoredAtom2063 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 10, 12}

def Fin15AnchoredAtom2064 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 10, 13}

def Fin15AnchoredAtom2065 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 10, 14}

def Fin15AnchoredAtom2066 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 11, 12}

def Fin15AnchoredAtom2067 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 11, 13}

def Fin15AnchoredAtom2068 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 11, 14}

def Fin15AnchoredAtom2069 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 12, 13}

def Fin15AnchoredAtom2070 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 12, 14}

def Fin15AnchoredAtom2071 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 13, 14}

def Fin15AnchoredAtom2072 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 9, 10}

def Fin15AnchoredAtom2074 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 9, 12}

def Fin15AnchoredAtom2075 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 9, 13}

def Fin15AnchoredAtom2076 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 9, 14}

def Fin15AnchoredAtom2078 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 10, 12}

def Fin15AnchoredAtom2079 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 10, 13}

def Fin15AnchoredAtom2080 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 10, 14}

def Fin15AnchoredAtom2084 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 12, 13}

def Fin15AnchoredAtom2085 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 12, 14}

def Fin15AnchoredAtom2086 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 13, 14}

def Fin15AnchoredAtom2087 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 9, 10, 11}

def Fin15AnchoredAtom2088 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 9, 10, 12}

def Fin15AnchoredAtom2089 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 9, 10, 13}

def Fin15AnchoredAtom2090 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 9, 10, 14}

def Fin15AnchoredAtom2091 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 9, 11, 12}

def Fin15AnchoredAtom2092 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 9, 11, 13}

def Fin15AnchoredAtom2093 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 9, 11, 14}

def Fin15AnchoredAtom2094 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 9, 12, 13}

def Fin15AnchoredAtom2095 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 9, 12, 14}

def Fin15AnchoredAtom2096 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 9, 13, 14}

def Fin15AnchoredAtom2097 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 10, 11, 12}

def Fin15AnchoredAtom2098 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 10, 11, 13}

def Fin15AnchoredAtom2099 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 10, 11, 14}

def Fin15AnchoredAtom2100 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 10, 12, 13}

def Fin15AnchoredAtom2101 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 10, 12, 14}

def Fin15AnchoredAtom2102 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 10, 13, 14}

def Fin15AnchoredAtom2103 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 11, 12, 13}

def Fin15AnchoredAtom2104 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 11, 12, 14}

def Fin15AnchoredAtom2105 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 11, 13, 14}

def Fin15AnchoredAtom2106 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 1, 12, 13, 14}

def Fin15AnchoredAtom2107 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 5}

def Fin15AnchoredAtom2108 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 6}

def Fin15AnchoredAtom2109 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 7}

def Fin15AnchoredAtom2110 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 8}

def Fin15AnchoredAtom2111 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 9}

def Fin15AnchoredAtom2112 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 10}

def Fin15AnchoredAtom2113 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 11}

def Fin15AnchoredAtom2114 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 12}

def Fin15AnchoredAtom2115 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 13}

def Fin15AnchoredAtom2116 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 14}

def Fin15AnchoredAtom2117 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 6}

def Fin15AnchoredAtom2118 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 7}

def Fin15AnchoredAtom2119 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 8}

def Fin15AnchoredAtom2120 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 9}

def Fin15AnchoredAtom2121 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 10}

def Fin15AnchoredAtom2122 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 11}

def Fin15AnchoredAtom2123 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 12}

def Fin15AnchoredAtom2124 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 13}

def Fin15AnchoredAtom2125 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 14}

def Fin15AnchoredAtom2126 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 7}

def Fin15AnchoredAtom2127 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 8}

def Fin15AnchoredAtom2128 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 9}

def Fin15AnchoredAtom2129 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 10}

def Fin15AnchoredAtom2130 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 11}

def Fin15AnchoredAtom2131 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 12}

def Fin15AnchoredAtom2132 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 13}

def Fin15AnchoredAtom2133 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 14}

def Fin15AnchoredAtom2134 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 8}

def Fin15AnchoredAtom2135 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 9}

def Fin15AnchoredAtom2136 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 10}

def Fin15AnchoredAtom2137 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 11}

def Fin15AnchoredAtom2138 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 12}

def Fin15AnchoredAtom2139 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 13}

def Fin15AnchoredAtom2140 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 14}

def Fin15AnchoredAtom2141 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 9}

def Fin15AnchoredAtom2142 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 10}

def Fin15AnchoredAtom2144 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 12}

def Fin15AnchoredAtom2145 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 13}

def Fin15AnchoredAtom2146 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 14}

def Fin15AnchoredAtom2147 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 10}

def Fin15AnchoredAtom2148 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 11}

def Fin15AnchoredAtom2149 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 12}

def Fin15AnchoredAtom2150 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 13}

def Fin15AnchoredAtom2151 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 14}

def Fin15AnchoredAtom2152 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 10, 11}

def Fin15AnchoredAtom2153 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 10, 12}

def Fin15AnchoredAtom2154 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 10, 13}

def Fin15AnchoredAtom2155 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 10, 14}

def Fin15AnchoredAtom2156 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 11, 12}

def Fin15AnchoredAtom2157 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 11, 13}

def Fin15AnchoredAtom2158 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 11, 14}

def Fin15AnchoredAtom2159 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 12, 13}

def Fin15AnchoredAtom2160 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 12, 14}

def Fin15AnchoredAtom2161 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 13, 14}

def Fin15AnchoredAtom2162 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 6}

def Fin15AnchoredAtom2163 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 7}

def Fin15AnchoredAtom2164 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 8}

def Fin15AnchoredAtom2165 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 9}

def Fin15AnchoredAtom2166 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 10}

def Fin15AnchoredAtom2167 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 11}

def Fin15AnchoredAtom2168 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 12}

def Fin15AnchoredAtom2169 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 13}

def Fin15AnchoredAtom2170 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 14}

def Fin15AnchoredAtom2171 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 7}

def Fin15AnchoredAtom2172 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 8}

def Fin15AnchoredAtom2173 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 9}

def Fin15AnchoredAtom2174 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 10}

def Fin15AnchoredAtom2175 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 11}

def Fin15AnchoredAtom2176 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 12}

def Fin15AnchoredAtom2177 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 13}

def Fin15AnchoredAtom2178 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 14}

def Fin15AnchoredAtom2179 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 8}

def Fin15AnchoredAtom2180 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 9}

def Fin15AnchoredAtom2181 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 10}

def Fin15AnchoredAtom2182 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 11}

def Fin15AnchoredAtom2183 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 12}

def Fin15AnchoredAtom2184 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 13}

def Fin15AnchoredAtom2185 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 14}

def Fin15AnchoredAtom2186 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 9}

def Fin15AnchoredAtom2187 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 10}

def Fin15AnchoredAtom2189 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 12}

def Fin15AnchoredAtom2190 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 13}

def Fin15AnchoredAtom2191 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 14}

def Fin15AnchoredAtom2192 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 10}

def Fin15AnchoredAtom2193 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 11}

def Fin15AnchoredAtom2194 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 12}

def Fin15AnchoredAtom2195 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 13}

def Fin15AnchoredAtom2196 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 14}

def Fin15AnchoredAtom2197 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 10, 11}

def Fin15AnchoredAtom2198 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 10, 12}

def Fin15AnchoredAtom2199 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 10, 13}

def Fin15AnchoredAtom2200 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 10, 14}

def Fin15AnchoredAtom2201 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 11, 12}

def Fin15AnchoredAtom2202 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 11, 13}

def Fin15AnchoredAtom2203 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 11, 14}

def Fin15AnchoredAtom2204 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 12, 13}

def Fin15AnchoredAtom2205 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 12, 14}

def Fin15AnchoredAtom2206 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 13, 14}

def Fin15AnchoredAtom2207 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 7}

def Fin15AnchoredAtom2208 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 8}

def Fin15AnchoredAtom2209 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 9}

def Fin15AnchoredAtom2210 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 10}

def Fin15AnchoredAtom2211 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 11}

def Fin15AnchoredAtom2212 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 12}

def Fin15AnchoredAtom2213 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 13}

def Fin15AnchoredAtom2214 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 14}

def Fin15AnchoredAtom2215 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 8}

def Fin15AnchoredAtom2216 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 9}

def Fin15AnchoredAtom2217 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 10}

def Fin15AnchoredAtom2218 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 11}

def Fin15AnchoredAtom2219 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 12}

def Fin15AnchoredAtom2220 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 13}

def Fin15AnchoredAtom2221 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 14}

def Fin15AnchoredAtom2222 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 9}

def Fin15AnchoredAtom2223 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 10}

def Fin15AnchoredAtom2225 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 12}

def Fin15AnchoredAtom2226 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 13}

def Fin15AnchoredAtom2227 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 14}

def Fin15AnchoredAtom2228 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 10}

def Fin15AnchoredAtom2229 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 11}

def Fin15AnchoredAtom2230 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 12}

def Fin15AnchoredAtom2231 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 13}

def Fin15AnchoredAtom2232 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 14}

def Fin15AnchoredAtom2233 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 10, 11}

def Fin15AnchoredAtom2234 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 10, 12}

def Fin15AnchoredAtom2235 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 10, 13}

def Fin15AnchoredAtom2236 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 10, 14}

def Fin15AnchoredAtom2237 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 11, 12}

def Fin15AnchoredAtom2238 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 11, 13}

def Fin15AnchoredAtom2239 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 11, 14}

def Fin15AnchoredAtom2240 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 12, 13}

def Fin15AnchoredAtom2241 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 12, 14}

def Fin15AnchoredAtom2242 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 13, 14}

def Fin15AnchoredAtom2243 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 8}

def Fin15AnchoredAtom2244 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 9}

def Fin15AnchoredAtom2245 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 10}

def Fin15AnchoredAtom2246 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 11}

def Fin15AnchoredAtom2247 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 12}

def Fin15AnchoredAtom2248 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 13}

def Fin15AnchoredAtom2249 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 14}

def Fin15AnchoredAtom2250 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 9}

def Fin15AnchoredAtom2251 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 10}

def Fin15AnchoredAtom2253 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 12}

def Fin15AnchoredAtom2254 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 13}

def Fin15AnchoredAtom2256 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 10}

def Fin15AnchoredAtom2257 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 11}

def Fin15AnchoredAtom2258 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 12}

def Fin15AnchoredAtom2259 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 13}

def Fin15AnchoredAtom2260 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 14}

def Fin15AnchoredAtom2261 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 10, 11}

def Fin15AnchoredAtom2262 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 10, 12}

def Fin15AnchoredAtom2263 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 10, 13}

def Fin15AnchoredAtom2264 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 10, 14}

def Fin15AnchoredAtom2265 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 11, 12}

def Fin15AnchoredAtom2266 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 11, 13}

def Fin15AnchoredAtom2267 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 11, 14}

def Fin15AnchoredAtom2268 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 12, 13}

def Fin15AnchoredAtom2269 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 12, 14}

def Fin15AnchoredAtom2270 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 13, 14}

def Fin15AnchoredAtom2271 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 9}

def Fin15AnchoredAtom2272 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 10}

def Fin15AnchoredAtom2274 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 12}

def Fin15AnchoredAtom2275 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 13}

def Fin15AnchoredAtom2276 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 14}

def Fin15AnchoredAtom2277 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 10}

def Fin15AnchoredAtom2278 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 11}

def Fin15AnchoredAtom2279 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 12}

def Fin15AnchoredAtom2280 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 13}

def Fin15AnchoredAtom2281 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 14}

def Fin15AnchoredAtom2282 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 10, 11}

def Fin15AnchoredAtom2283 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 10, 12}

def Fin15AnchoredAtom2284 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 10, 13}

def Fin15AnchoredAtom2285 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 10, 14}

def Fin15AnchoredAtom2286 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 11, 12}

def Fin15AnchoredAtom2287 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 11, 13}

def Fin15AnchoredAtom2288 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 11, 14}

def Fin15AnchoredAtom2289 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 12, 13}

def Fin15AnchoredAtom2290 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 12, 14}

def Fin15AnchoredAtom2291 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 13, 14}

def Fin15AnchoredAtom2292 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 9, 10}

def Fin15AnchoredAtom2294 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 9, 12}

def Fin15AnchoredAtom2296 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 9, 14}

def Fin15AnchoredAtom2298 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 10, 12}

def Fin15AnchoredAtom2299 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 10, 13}

def Fin15AnchoredAtom2304 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 12, 13}

def Fin15AnchoredAtom2305 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 12, 14}

def Fin15AnchoredAtom2307 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 9, 10, 11}

def Fin15AnchoredAtom2308 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 9, 10, 12}

def Fin15AnchoredAtom2309 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 9, 10, 13}

def Fin15AnchoredAtom2310 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 9, 10, 14}

def Fin15AnchoredAtom2311 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 9, 11, 12}

def Fin15AnchoredAtom2312 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 9, 11, 13}

def Fin15AnchoredAtom2313 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 9, 11, 14}

def Fin15AnchoredAtom2314 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 9, 12, 13}

def Fin15AnchoredAtom2315 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 9, 12, 14}

def Fin15AnchoredAtom2316 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 9, 13, 14}

def Fin15AnchoredAtom2317 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 10, 11, 12}

def Fin15AnchoredAtom2318 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 10, 11, 13}

def Fin15AnchoredAtom2319 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 10, 11, 14}

def Fin15AnchoredAtom2320 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 10, 12, 13}

def Fin15AnchoredAtom2321 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 10, 12, 14}

def Fin15AnchoredAtom2322 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 10, 13, 14}

def Fin15AnchoredAtom2323 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 11, 12, 13}

def Fin15AnchoredAtom2324 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 11, 12, 14}

def Fin15AnchoredAtom2325 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 11, 13, 14}

def Fin15AnchoredAtom2326 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 2, 12, 13, 14}

def Fin15AnchoredAtom2327 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 6}

def Fin15AnchoredAtom2328 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 7}

def Fin15AnchoredAtom2329 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 8}

def Fin15AnchoredAtom2330 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 9}

def Fin15AnchoredAtom2331 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 10}

def Fin15AnchoredAtom2332 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 11}

def Fin15AnchoredAtom2333 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 12}

def Fin15AnchoredAtom2334 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 13}

def Fin15AnchoredAtom2335 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 14}

def Fin15AnchoredAtom2336 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 7}

def Fin15AnchoredAtom2337 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 8}

def Fin15AnchoredAtom2338 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 9}

def Fin15AnchoredAtom2339 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 10}

def Fin15AnchoredAtom2340 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 11}

def Fin15AnchoredAtom2341 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 12}

def Fin15AnchoredAtom2342 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 13}

def Fin15AnchoredAtom2343 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 14}

def Fin15AnchoredAtom2344 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 8}

def Fin15AnchoredAtom2345 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 9}

def Fin15AnchoredAtom2346 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 10}

def Fin15AnchoredAtom2347 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 11}

def Fin15AnchoredAtom2348 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 12}

def Fin15AnchoredAtom2349 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 13}

def Fin15AnchoredAtom2350 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 14}

def Fin15AnchoredAtom2351 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 9}

def Fin15AnchoredAtom2352 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 10}

def Fin15AnchoredAtom2354 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 12}

def Fin15AnchoredAtom2355 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 13}

def Fin15AnchoredAtom2356 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 14}

def Fin15AnchoredAtom2357 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 10}

def Fin15AnchoredAtom2358 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 11}

def Fin15AnchoredAtom2359 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 12}

def Fin15AnchoredAtom2360 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 13}

def Fin15AnchoredAtom2361 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 14}

def Fin15AnchoredAtom2362 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 10, 11}

def Fin15AnchoredAtom2363 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 10, 12}

def Fin15AnchoredAtom2364 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 10, 13}

def Fin15AnchoredAtom2365 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 10, 14}

def Fin15AnchoredAtom2366 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 11, 12}

def Fin15AnchoredAtom2367 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 11, 13}

def Fin15AnchoredAtom2368 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 11, 14}

def Fin15AnchoredAtom2369 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 12, 13}

def Fin15AnchoredAtom2370 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 12, 14}

def Fin15AnchoredAtom2371 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 13, 14}

def Fin15AnchoredAtom2372 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 7}

def Fin15AnchoredAtom2373 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 8}

def Fin15AnchoredAtom2374 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 9}

def Fin15AnchoredAtom2375 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 10}

def Fin15AnchoredAtom2376 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 11}

def Fin15AnchoredAtom2377 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 12}

def Fin15AnchoredAtom2378 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 13}

def Fin15AnchoredAtom2379 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 14}

def Fin15AnchoredAtom2380 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 8}

def Fin15AnchoredAtom2381 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 9}

def Fin15AnchoredAtom2382 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 10}

def Fin15AnchoredAtom2383 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 11}

def Fin15AnchoredAtom2384 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 12}

def Fin15AnchoredAtom2385 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 13}

def Fin15AnchoredAtom2386 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 14}

def Fin15AnchoredAtom2387 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 9}

def Fin15AnchoredAtom2388 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 10}

def Fin15AnchoredAtom2390 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 12}

def Fin15AnchoredAtom2391 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 13}

def Fin15AnchoredAtom2392 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 14}

def Fin15AnchoredAtom2393 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 10}

def Fin15AnchoredAtom2394 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 11}

def Fin15AnchoredAtom2395 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 12}

def Fin15AnchoredAtom2396 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 13}

def Fin15AnchoredAtom2397 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 14}

def Fin15AnchoredAtom2398 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 10, 11}

def Fin15AnchoredAtom2399 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 10, 12}

def Fin15AnchoredAtom2400 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 10, 13}

def Fin15AnchoredAtom2401 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 10, 14}

def Fin15AnchoredAtom2402 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 11, 12}

def Fin15AnchoredAtom2403 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 11, 13}

def Fin15AnchoredAtom2404 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 11, 14}

def Fin15AnchoredAtom2405 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 12, 13}

def Fin15AnchoredAtom2406 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 12, 14}

def Fin15AnchoredAtom2407 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 13, 14}

def Fin15AnchoredAtom2408 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 8}

def Fin15AnchoredAtom2409 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 9}

def Fin15AnchoredAtom2410 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 10}

def Fin15AnchoredAtom2411 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 11}

def Fin15AnchoredAtom2412 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 12}

def Fin15AnchoredAtom2413 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 13}

def Fin15AnchoredAtom2414 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 14}

def Fin15AnchoredAtom2415 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 9}

def Fin15AnchoredAtom2416 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 10}

def Fin15AnchoredAtom2418 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 12}

def Fin15AnchoredAtom2419 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 13}

def Fin15AnchoredAtom2420 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 14}

def Fin15AnchoredAtom2421 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 10}

def Fin15AnchoredAtom2422 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 11}

def Fin15AnchoredAtom2423 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 12}

def Fin15AnchoredAtom2424 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 13}

def Fin15AnchoredAtom2425 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 14}

def Fin15AnchoredAtom2426 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 10, 11}

def Fin15AnchoredAtom2427 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 10, 12}

def Fin15AnchoredAtom2428 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 10, 13}

def Fin15AnchoredAtom2429 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 10, 14}

def Fin15AnchoredAtom2430 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 11, 12}

def Fin15AnchoredAtom2431 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 11, 13}

def Fin15AnchoredAtom2433 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 12, 13}

def Fin15AnchoredAtom2434 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 12, 14}

def Fin15AnchoredAtom2435 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 13, 14}

def Fin15AnchoredAtom2436 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 9}

def Fin15AnchoredAtom2437 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 10}

def Fin15AnchoredAtom2439 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 12}

def Fin15AnchoredAtom2440 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 13}

def Fin15AnchoredAtom2441 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 14}

def Fin15AnchoredAtom2442 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 10}

def Fin15AnchoredAtom2443 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 11}

def Fin15AnchoredAtom2444 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 12}

def Fin15AnchoredAtom2445 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 13}

def Fin15AnchoredAtom2446 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 14}

def Fin15AnchoredAtom2447 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 10, 11}

def Fin15AnchoredAtom2448 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 10, 12}

def Fin15AnchoredAtom2449 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 10, 13}

def Fin15AnchoredAtom2450 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 10, 14}

def Fin15AnchoredAtom2451 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 11, 12}

def Fin15AnchoredAtom2452 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 11, 13}

def Fin15AnchoredAtom2453 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 11, 14}

def Fin15AnchoredAtom2454 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 12, 13}

def Fin15AnchoredAtom2455 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 12, 14}

def Fin15AnchoredAtom2456 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 13, 14}

def Fin15AnchoredAtom2457 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 9, 10}

def Fin15AnchoredAtom2459 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 9, 12}

def Fin15AnchoredAtom2460 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 9, 13}

def Fin15AnchoredAtom2461 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 9, 14}

def Fin15AnchoredAtom2463 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 10, 12}

def Fin15AnchoredAtom2464 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 10, 13}

def Fin15AnchoredAtom2465 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 10, 14}

def Fin15AnchoredAtom2469 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 12, 13}

def Fin15AnchoredAtom2470 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 12, 14}

def Fin15AnchoredAtom2471 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 13, 14}

def Fin15AnchoredAtom2472 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 9, 10, 11}

def Fin15AnchoredAtom2473 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 9, 10, 12}

def Fin15AnchoredAtom2474 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 9, 10, 13}

def Fin15AnchoredAtom2475 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 9, 10, 14}

def Fin15AnchoredAtom2476 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 9, 11, 12}

def Fin15AnchoredAtom2477 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 9, 11, 13}

def Fin15AnchoredAtom2478 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 9, 11, 14}

def Fin15AnchoredAtom2479 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 9, 12, 13}

def Fin15AnchoredAtom2480 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 9, 12, 14}

def Fin15AnchoredAtom2481 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 9, 13, 14}

def Fin15AnchoredAtom2482 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 10, 11, 12}

def Fin15AnchoredAtom2483 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 10, 11, 13}

def Fin15AnchoredAtom2484 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 10, 11, 14}

def Fin15AnchoredAtom2485 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 10, 12, 13}

def Fin15AnchoredAtom2486 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 10, 12, 14}

def Fin15AnchoredAtom2487 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 10, 13, 14}

def Fin15AnchoredAtom2488 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 11, 12, 13}

def Fin15AnchoredAtom2489 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 11, 12, 14}

def Fin15AnchoredAtom2490 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 11, 13, 14}

def Fin15AnchoredAtom2491 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 3, 12, 13, 14}

def Fin15AnchoredAtom2492 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 7}

def Fin15AnchoredAtom2493 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 8}

def Fin15AnchoredAtom2494 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 9}

def Fin15AnchoredAtom2495 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 10}

def Fin15AnchoredAtom2496 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 11}

def Fin15AnchoredAtom2497 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 12}

def Fin15AnchoredAtom2498 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 13}

def Fin15AnchoredAtom2499 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 14}

def Fin15AnchoredAtom2500 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 8}

def Fin15AnchoredAtom2501 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 9}

def Fin15AnchoredAtom2502 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 10}

def Fin15AnchoredAtom2503 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 11}

def Fin15AnchoredAtom2504 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 12}

def Fin15AnchoredAtom2505 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 13}

def Fin15AnchoredAtom2506 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 14}

def Fin15AnchoredAtom2507 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 9}

def Fin15AnchoredAtom2508 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 10}

def Fin15AnchoredAtom2510 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 12}

def Fin15AnchoredAtom2511 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 13}

def Fin15AnchoredAtom2512 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 14}

def Fin15AnchoredAtom2513 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 10}

def Fin15AnchoredAtom2514 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 11}

def Fin15AnchoredAtom2515 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 12}

def Fin15AnchoredAtom2516 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 13}

def Fin15AnchoredAtom2517 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 14}

def Fin15AnchoredAtom2518 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 10, 11}

def Fin15AnchoredAtom2519 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 10, 12}

def Fin15AnchoredAtom2520 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 10, 13}

def Fin15AnchoredAtom2521 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 10, 14}

def Fin15AnchoredAtom2522 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 11, 12}

def Fin15AnchoredAtom2523 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 11, 13}

def Fin15AnchoredAtom2524 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 11, 14}

def Fin15AnchoredAtom2525 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 12, 13}

def Fin15AnchoredAtom2526 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 12, 14}

def Fin15AnchoredAtom2527 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 13, 14}

def Fin15AnchoredAtom2528 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 8}

def Fin15AnchoredAtom2529 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 9}

def Fin15AnchoredAtom2530 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 10}

def Fin15AnchoredAtom2531 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 11}

def Fin15AnchoredAtom2532 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 12}

def Fin15AnchoredAtom2533 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 13}

def Fin15AnchoredAtom2534 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 14}

def Fin15AnchoredAtom2535 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 9}

def Fin15AnchoredAtom2536 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 10}

def Fin15AnchoredAtom2538 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 12}

def Fin15AnchoredAtom2539 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 13}

def Fin15AnchoredAtom2540 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 14}

def Fin15AnchoredAtom2541 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 10}

def Fin15AnchoredAtom2542 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 11}

def Fin15AnchoredAtom2543 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 12}

def Fin15AnchoredAtom2544 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 13}

def Fin15AnchoredAtom2545 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 14}

def Fin15AnchoredAtom2546 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 10, 11}

def Fin15AnchoredAtom2547 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 10, 12}

def Fin15AnchoredAtom2548 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 10, 13}

def Fin15AnchoredAtom2549 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 10, 14}

def Fin15AnchoredAtom2550 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 11, 12}

def Fin15AnchoredAtom2551 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 11, 13}

def Fin15AnchoredAtom2552 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 11, 14}

def Fin15AnchoredAtom2553 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 12, 13}

def Fin15AnchoredAtom2554 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 12, 14}

def Fin15AnchoredAtom2555 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 13, 14}

def Fin15AnchoredAtom2556 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 9}

def Fin15AnchoredAtom2557 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 10}

def Fin15AnchoredAtom2559 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 12}

def Fin15AnchoredAtom2560 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 13}

def Fin15AnchoredAtom2561 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 14}

def Fin15AnchoredAtom2562 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 10}

def Fin15AnchoredAtom2563 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 11}

def Fin15AnchoredAtom2564 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 12}

def Fin15AnchoredAtom2565 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 13}

def Fin15AnchoredAtom2566 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 14}

def Fin15AnchoredAtom2567 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 10, 11}

def Fin15AnchoredAtom2568 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 10, 12}

def Fin15AnchoredAtom2569 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 10, 13}

def Fin15AnchoredAtom2570 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 10, 14}

def Fin15AnchoredAtom2571 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 11, 12}

def Fin15AnchoredAtom2572 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 11, 13}

def Fin15AnchoredAtom2573 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 11, 14}

def Fin15AnchoredAtom2574 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 12, 13}

def Fin15AnchoredAtom2575 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 12, 14}

def Fin15AnchoredAtom2576 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 13, 14}

def Fin15AnchoredAtom2577 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 9, 10}

def Fin15AnchoredAtom2579 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 9, 12}

def Fin15AnchoredAtom2580 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 9, 13}

def Fin15AnchoredAtom2581 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 9, 14}

def Fin15AnchoredAtom2583 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 10, 12}

def Fin15AnchoredAtom2584 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 10, 13}

def Fin15AnchoredAtom2585 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 10, 14}

def Fin15AnchoredAtom2589 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 12, 13}

def Fin15AnchoredAtom2590 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 12, 14}

def Fin15AnchoredAtom2591 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 13, 14}

def Fin15AnchoredAtom2592 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 9, 10, 11}

def Fin15AnchoredAtom2593 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 9, 10, 12}

def Fin15AnchoredAtom2594 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 9, 10, 13}

def Fin15AnchoredAtom2595 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 9, 10, 14}

def Fin15AnchoredAtom2596 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 9, 11, 12}

def Fin15AnchoredAtom2597 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 9, 11, 13}

def Fin15AnchoredAtom2598 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 9, 11, 14}

def Fin15AnchoredAtom2599 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 9, 12, 13}

def Fin15AnchoredAtom2600 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 9, 12, 14}

def Fin15AnchoredAtom2601 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 9, 13, 14}

def Fin15AnchoredAtom2602 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 10, 11, 12}

def Fin15AnchoredAtom2603 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 10, 11, 13}

def Fin15AnchoredAtom2604 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 10, 11, 14}

def Fin15AnchoredAtom2605 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 10, 12, 13}

def Fin15AnchoredAtom2606 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 10, 12, 14}

def Fin15AnchoredAtom2607 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 10, 13, 14}

def Fin15AnchoredAtom2608 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 11, 12, 13}

def Fin15AnchoredAtom2609 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 11, 12, 14}

def Fin15AnchoredAtom2611 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 4, 12, 13, 14}

def Fin15AnchoredAtom2612 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 8}

def Fin15AnchoredAtom2613 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 9}

def Fin15AnchoredAtom2614 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 10}

def Fin15AnchoredAtom2615 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 11}

def Fin15AnchoredAtom2616 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 12}

def Fin15AnchoredAtom2617 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 13}

def Fin15AnchoredAtom2618 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 14}

def Fin15AnchoredAtom2619 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 9}

def Fin15AnchoredAtom2620 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 10}

def Fin15AnchoredAtom2622 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 12}

def Fin15AnchoredAtom2623 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 13}

def Fin15AnchoredAtom2624 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 14}

def Fin15AnchoredAtom2625 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 10}

def Fin15AnchoredAtom2626 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 11}

def Fin15AnchoredAtom2627 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 12}

def Fin15AnchoredAtom2628 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 13}

def Fin15AnchoredAtom2629 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 14}

def Fin15AnchoredAtom2630 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 10, 11}

def Fin15AnchoredAtom2631 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 10, 12}

def Fin15AnchoredAtom2632 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 10, 13}

def Fin15AnchoredAtom2633 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 10, 14}

def Fin15AnchoredAtom2634 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 11, 12}

def Fin15AnchoredAtom2635 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 11, 13}

def Fin15AnchoredAtom2636 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 11, 14}

def Fin15AnchoredAtom2637 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 12, 13}

def Fin15AnchoredAtom2638 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 12, 14}

def Fin15AnchoredAtom2639 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 13, 14}

def Fin15AnchoredAtom2640 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 9}

def Fin15AnchoredAtom2641 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 10}

def Fin15AnchoredAtom2643 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 12}

def Fin15AnchoredAtom2644 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 13}

def Fin15AnchoredAtom2645 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 14}

def Fin15AnchoredAtom2646 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 10}

def Fin15AnchoredAtom2647 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 11}

def Fin15AnchoredAtom2648 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 12}

def Fin15AnchoredAtom2649 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 13}

def Fin15AnchoredAtom2650 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 14}

def Fin15AnchoredAtom2651 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 10, 11}

def Fin15AnchoredAtom2652 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 10, 12}

def Fin15AnchoredAtom2653 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 10, 13}

def Fin15AnchoredAtom2654 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 10, 14}

def Fin15AnchoredAtom2655 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 11, 12}

def Fin15AnchoredAtom2656 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 11, 13}

def Fin15AnchoredAtom2657 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 11, 14}

def Fin15AnchoredAtom2658 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 12, 13}

def Fin15AnchoredAtom2659 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 12, 14}

def Fin15AnchoredAtom2660 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 13, 14}

def Fin15AnchoredAtom2661 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 9, 10}

def Fin15AnchoredAtom2663 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 9, 12}

def Fin15AnchoredAtom2664 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 9, 13}

def Fin15AnchoredAtom2665 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 9, 14}

def Fin15AnchoredAtom2667 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 10, 12}

def Fin15AnchoredAtom2668 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 10, 13}

def Fin15AnchoredAtom2669 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 10, 14}

def Fin15AnchoredAtom2673 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 12, 13}

def Fin15AnchoredAtom2674 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 12, 14}

def Fin15AnchoredAtom2675 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 13, 14}

def Fin15AnchoredAtom2676 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 9, 10, 11}

def Fin15AnchoredAtom2677 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 9, 10, 12}

def Fin15AnchoredAtom2678 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 9, 10, 13}

def Fin15AnchoredAtom2679 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 9, 10, 14}

def Fin15AnchoredAtom2680 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 9, 11, 12}

def Fin15AnchoredAtom2681 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 9, 11, 13}

def Fin15AnchoredAtom2682 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 9, 11, 14}

def Fin15AnchoredAtom2683 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 9, 12, 13}

def Fin15AnchoredAtom2684 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 9, 12, 14}

def Fin15AnchoredAtom2685 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 9, 13, 14}

def Fin15AnchoredAtom2686 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 10, 11, 12}

def Fin15AnchoredAtom2687 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 10, 11, 13}

def Fin15AnchoredAtom2688 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 10, 11, 14}

def Fin15AnchoredAtom2689 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 10, 12, 13}

def Fin15AnchoredAtom2690 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 10, 12, 14}

def Fin15AnchoredAtom2691 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 10, 13, 14}

def Fin15AnchoredAtom2692 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 11, 12, 13}

def Fin15AnchoredAtom2693 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 11, 12, 14}

def Fin15AnchoredAtom2694 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 11, 13, 14}

def Fin15AnchoredAtom2695 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 5, 12, 13, 14}

def Fin15AnchoredAtom2696 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 9}

def Fin15AnchoredAtom2697 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 10}

def Fin15AnchoredAtom2699 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 12}

def Fin15AnchoredAtom2700 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 13}

def Fin15AnchoredAtom2701 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 14}

def Fin15AnchoredAtom2702 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 10}

def Fin15AnchoredAtom2703 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 11}

def Fin15AnchoredAtom2704 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 12}

def Fin15AnchoredAtom2705 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 13}

def Fin15AnchoredAtom2706 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 14}

def Fin15AnchoredAtom2707 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 10, 11}

def Fin15AnchoredAtom2708 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 10, 12}

def Fin15AnchoredAtom2709 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 10, 13}

def Fin15AnchoredAtom2710 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 10, 14}

def Fin15AnchoredAtom2711 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 11, 12}

def Fin15AnchoredAtom2712 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 11, 13}

def Fin15AnchoredAtom2713 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 11, 14}

def Fin15AnchoredAtom2714 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 12, 13}

def Fin15AnchoredAtom2715 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 12, 14}

def Fin15AnchoredAtom2716 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 13, 14}

def Fin15AnchoredAtom2717 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 9, 10}

def Fin15AnchoredAtom2719 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 9, 12}

def Fin15AnchoredAtom2720 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 9, 13}

def Fin15AnchoredAtom2721 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 9, 14}

def Fin15AnchoredAtom2723 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 10, 12}

def Fin15AnchoredAtom2724 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 10, 13}

def Fin15AnchoredAtom2725 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 10, 14}

def Fin15AnchoredAtom2729 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 12, 13}

def Fin15AnchoredAtom2730 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 12, 14}

def Fin15AnchoredAtom2731 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 13, 14}

def Fin15AnchoredAtom2732 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 9, 10, 11}

def Fin15AnchoredAtom2733 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 9, 10, 12}

def Fin15AnchoredAtom2734 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 9, 10, 13}

def Fin15AnchoredAtom2735 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 9, 10, 14}

def Fin15AnchoredAtom2736 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 9, 11, 12}

def Fin15AnchoredAtom2737 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 9, 11, 13}

def Fin15AnchoredAtom2738 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 9, 11, 14}

def Fin15AnchoredAtom2739 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 9, 12, 13}

def Fin15AnchoredAtom2740 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 9, 12, 14}

def Fin15AnchoredAtom2741 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 9, 13, 14}

def Fin15AnchoredAtom2742 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 10, 11, 12}

def Fin15AnchoredAtom2743 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 10, 11, 13}

def Fin15AnchoredAtom2744 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 10, 11, 14}

def Fin15AnchoredAtom2745 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 10, 12, 13}

def Fin15AnchoredAtom2746 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 10, 12, 14}

def Fin15AnchoredAtom2747 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 10, 13, 14}

def Fin15AnchoredAtom2748 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 11, 12, 13}

def Fin15AnchoredAtom2749 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 11, 12, 14}

def Fin15AnchoredAtom2751 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 6, 12, 13, 14}

def Fin15AnchoredAtom2752 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 9, 10}

def Fin15AnchoredAtom2754 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 9, 12}

def Fin15AnchoredAtom2755 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 9, 13}

def Fin15AnchoredAtom2756 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 9, 14}

def Fin15AnchoredAtom2758 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 10, 12}

def Fin15AnchoredAtom2759 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 10, 13}

def Fin15AnchoredAtom2760 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 10, 14}

def Fin15AnchoredAtom2764 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 12, 13}

def Fin15AnchoredAtom2765 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 12, 14}

def Fin15AnchoredAtom2766 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 13, 14}

def Fin15AnchoredAtom2767 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 9, 10, 11}

def Fin15AnchoredAtom2768 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 9, 10, 12}

def Fin15AnchoredAtom2769 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 9, 10, 13}

def Fin15AnchoredAtom2770 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 9, 10, 14}

def Fin15AnchoredAtom2771 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 9, 11, 12}

def Fin15AnchoredAtom2772 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 9, 11, 13}

def Fin15AnchoredAtom2773 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 9, 11, 14}

def Fin15AnchoredAtom2774 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 9, 12, 13}

def Fin15AnchoredAtom2775 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 9, 12, 14}

def Fin15AnchoredAtom2776 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 9, 13, 14}

def Fin15AnchoredAtom2777 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 10, 11, 12}

def Fin15AnchoredAtom2778 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 10, 11, 13}

def Fin15AnchoredAtom2779 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 10, 11, 14}

def Fin15AnchoredAtom2780 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 10, 12, 13}

def Fin15AnchoredAtom2781 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 10, 12, 14}

def Fin15AnchoredAtom2782 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 10, 13, 14}

def Fin15AnchoredAtom2783 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 11, 12, 13}

def Fin15AnchoredAtom2784 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 11, 12, 14}

def Fin15AnchoredAtom2785 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 11, 13, 14}

def Fin15AnchoredAtom2786 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 7, 12, 13, 14}

def Fin15AnchoredAtom2788 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 8, 9, 10, 12}

def Fin15AnchoredAtom2789 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 8, 9, 10, 13}

def Fin15AnchoredAtom2790 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 8, 9, 10, 14}

def Fin15AnchoredAtom2794 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 8, 9, 12, 13}

def Fin15AnchoredAtom2795 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 8, 9, 12, 14}

def Fin15AnchoredAtom2796 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 8, 9, 13, 14}

def Fin15AnchoredAtom2800 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 8, 10, 12, 13}

def Fin15AnchoredAtom2801 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 8, 10, 12, 14}

def Fin15AnchoredAtom2802 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 8, 10, 13, 14}

def Fin15AnchoredAtom2806 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 8, 12, 13, 14}

def Fin15AnchoredAtom2807 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 9, 10, 11, 12}

def Fin15AnchoredAtom2808 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 9, 10, 11, 13}

def Fin15AnchoredAtom2809 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 9, 10, 11, 14}

def Fin15AnchoredAtom2810 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 9, 10, 12, 13}

def Fin15AnchoredAtom2811 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 9, 10, 12, 14}

def Fin15AnchoredAtom2812 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 9, 10, 13, 14}

def Fin15AnchoredAtom2813 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 9, 11, 12, 13}

def Fin15AnchoredAtom2814 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 9, 11, 12, 14}

def Fin15AnchoredAtom2815 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 9, 11, 13, 14}

def Fin15AnchoredAtom2816 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 9, 12, 13, 14}

def Fin15AnchoredAtom2817 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 10, 11, 12, 13}

def Fin15AnchoredAtom2818 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 10, 11, 12, 14}

def Fin15AnchoredAtom2819 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 10, 11, 13, 14}

def Fin15AnchoredAtom2820 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 10, 12, 13, 14}

def Fin15AnchoredAtom2821 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {0, 11, 12, 13, 14}

def Fin15AnchoredAtom2822 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 5}

def Fin15AnchoredAtom2823 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 6}

def Fin15AnchoredAtom2824 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 7}

def Fin15AnchoredAtom2825 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 8}

def Fin15AnchoredAtom2826 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 9}

def Fin15AnchoredAtom2827 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 10}

def Fin15AnchoredAtom2828 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 11}

def Fin15AnchoredAtom2829 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 12}

def Fin15AnchoredAtom2830 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 13}

def Fin15AnchoredAtom2831 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 14}

def Fin15AnchoredAtom2832 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 6}

def Fin15AnchoredAtom2833 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 7}

def Fin15AnchoredAtom2834 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 8}

def Fin15AnchoredAtom2835 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 9}

def Fin15AnchoredAtom2836 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 10}

def Fin15AnchoredAtom2837 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 11}

def Fin15AnchoredAtom2838 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 12}

def Fin15AnchoredAtom2839 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 13}

def Fin15AnchoredAtom2840 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 14}

def Fin15AnchoredAtom2841 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 7}

def Fin15AnchoredAtom2842 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 8}

def Fin15AnchoredAtom2843 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 9}

def Fin15AnchoredAtom2844 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 10}

def Fin15AnchoredAtom2845 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 11}

def Fin15AnchoredAtom2846 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 12}

def Fin15AnchoredAtom2847 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 13}

def Fin15AnchoredAtom2848 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 14}

def Fin15AnchoredAtom2849 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 8}

def Fin15AnchoredAtom2850 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 9}

def Fin15AnchoredAtom2851 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 10}

def Fin15AnchoredAtom2852 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 11}

def Fin15AnchoredAtom2853 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 12}

def Fin15AnchoredAtom2854 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 13}

def Fin15AnchoredAtom2855 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 14}

def Fin15AnchoredAtom2857 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 10}

def Fin15AnchoredAtom2859 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 12}

def Fin15AnchoredAtom2860 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 13}

def Fin15AnchoredAtom2861 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 14}

def Fin15AnchoredAtom2862 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 9, 10}

def Fin15AnchoredAtom2863 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 9, 11}

def Fin15AnchoredAtom2864 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 9, 12}

def Fin15AnchoredAtom2865 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 9, 13}

def Fin15AnchoredAtom2866 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 9, 14}

def Fin15AnchoredAtom2867 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 10, 11}

def Fin15AnchoredAtom2868 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 10, 12}

def Fin15AnchoredAtom2869 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 10, 13}

def Fin15AnchoredAtom2870 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 10, 14}

def Fin15AnchoredAtom2872 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 11, 13}

def Fin15AnchoredAtom2873 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 11, 14}

def Fin15AnchoredAtom2874 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 12, 13}

def Fin15AnchoredAtom2875 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 12, 14}

def Fin15AnchoredAtom2876 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 13, 14}

def Fin15AnchoredAtom2877 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 6}

def Fin15AnchoredAtom2878 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 7}

def Fin15AnchoredAtom2880 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 9}

def Fin15AnchoredAtom2881 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 10}

def Fin15AnchoredAtom2882 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 11}

def Fin15AnchoredAtom2883 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 12}

def Fin15AnchoredAtom2884 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 13}

def Fin15AnchoredAtom2885 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 14}

def Fin15AnchoredAtom2886 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 7}

def Fin15AnchoredAtom2887 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 8}

def Fin15AnchoredAtom2888 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 9}

def Fin15AnchoredAtom2889 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 10}

def Fin15AnchoredAtom2890 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 11}

def Fin15AnchoredAtom2891 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 12}

def Fin15AnchoredAtom2892 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 13}

def Fin15AnchoredAtom2893 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 14}

def Fin15AnchoredAtom2894 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 8}

def Fin15AnchoredAtom2895 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 9}

def Fin15AnchoredAtom2896 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 10}

def Fin15AnchoredAtom2897 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 11}

def Fin15AnchoredAtom2898 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 12}

def Fin15AnchoredAtom2899 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 13}

def Fin15AnchoredAtom2900 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 14}

def Fin15AnchoredAtom2901 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 9}

def Fin15AnchoredAtom2906 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 14}

def Fin15AnchoredAtom2907 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 9, 10}

def Fin15AnchoredAtom2908 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 9, 11}

def Fin15AnchoredAtom2909 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 9, 12}

def Fin15AnchoredAtom2910 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 9, 13}

def Fin15AnchoredAtom2911 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 9, 14}

def Fin15AnchoredAtom2912 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 10, 11}

def Fin15AnchoredAtom2913 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 10, 12}

def Fin15AnchoredAtom2914 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 10, 13}

def Fin15AnchoredAtom2915 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 10, 14}

def Fin15AnchoredAtom2916 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 11, 12}

def Fin15AnchoredAtom2917 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 11, 13}

def Fin15AnchoredAtom2919 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 12, 13}

def Fin15AnchoredAtom2920 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 12, 14}

def Fin15AnchoredAtom2921 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 13, 14}

def Fin15AnchoredAtom2922 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 7}

def Fin15AnchoredAtom2923 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 8}

def Fin15AnchoredAtom2924 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 9}

def Fin15AnchoredAtom2925 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 10}

def Fin15AnchoredAtom2926 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 11}

def Fin15AnchoredAtom2927 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 12}

def Fin15AnchoredAtom2928 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 13}

def Fin15AnchoredAtom2929 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 14}

def Fin15AnchoredAtom2930 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 8}

def Fin15AnchoredAtom2931 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 9}

def Fin15AnchoredAtom2932 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 10}

def Fin15AnchoredAtom2933 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 11}

def Fin15AnchoredAtom2934 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 12}

def Fin15AnchoredAtom2935 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 13}

def Fin15AnchoredAtom2936 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 14}

def Fin15AnchoredAtom2937 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 9}

def Fin15AnchoredAtom2938 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 10}

def Fin15AnchoredAtom2940 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 12}

def Fin15AnchoredAtom2941 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 13}

def Fin15AnchoredAtom2943 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 9, 10}

def Fin15AnchoredAtom2944 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 9, 11}

def Fin15AnchoredAtom2945 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 9, 12}

def Fin15AnchoredAtom2946 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 9, 13}

def Fin15AnchoredAtom2947 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 9, 14}

def Fin15AnchoredAtom2948 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 10, 11}

def Fin15AnchoredAtom2949 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 10, 12}

def Fin15AnchoredAtom2950 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 10, 13}

def Fin15AnchoredAtom2951 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 10, 14}

def Fin15AnchoredAtom2955 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 12, 13}

def Fin15AnchoredAtom2956 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 12, 14}

def Fin15AnchoredAtom2957 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 13, 14}

def Fin15AnchoredAtom2958 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 8}

def Fin15AnchoredAtom2959 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 9}

def Fin15AnchoredAtom2960 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 10}

def Fin15AnchoredAtom2961 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 11}

def Fin15AnchoredAtom2962 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 12}

def Fin15AnchoredAtom2963 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 13}

def Fin15AnchoredAtom2964 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 14}

def Fin15AnchoredAtom2965 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 9}

def Fin15AnchoredAtom2966 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 10}

def Fin15AnchoredAtom2970 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 14}

def Fin15AnchoredAtom2971 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 9, 10}

def Fin15AnchoredAtom2972 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 9, 11}

def Fin15AnchoredAtom2973 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 9, 12}

def Fin15AnchoredAtom2974 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 9, 13}

def Fin15AnchoredAtom2975 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 9, 14}

def Fin15AnchoredAtom2976 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 10, 11}

def Fin15AnchoredAtom2977 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 10, 12}

def Fin15AnchoredAtom2978 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 10, 13}

def Fin15AnchoredAtom2979 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 10, 14}

def Fin15AnchoredAtom2980 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 11, 12}

def Fin15AnchoredAtom2983 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 12, 13}

def Fin15AnchoredAtom2984 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 12, 14}

def Fin15AnchoredAtom2985 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 13, 14}

def Fin15AnchoredAtom2986 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 8, 9}

def Fin15AnchoredAtom2987 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 8, 10}

def Fin15AnchoredAtom2991 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 8, 14}

def Fin15AnchoredAtom2992 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 9, 10}

def Fin15AnchoredAtom2993 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 9, 11}

def Fin15AnchoredAtom2994 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 9, 12}

def Fin15AnchoredAtom2995 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 9, 13}

def Fin15AnchoredAtom2996 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 9, 14}

def Fin15AnchoredAtom2997 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 10, 11}

def Fin15AnchoredAtom2998 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 10, 12}

def Fin15AnchoredAtom2999 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 10, 13}

def Fin15AnchoredAtom3000 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 10, 14}

def Fin15AnchoredAtom3001 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 11, 12}

def Fin15AnchoredAtom3004 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 12, 13}

def Fin15AnchoredAtom3005 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 12, 14}

def Fin15AnchoredAtom3006 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 13, 14}

def Fin15AnchoredAtom3007 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 8, 9, 10}

def Fin15AnchoredAtom3013 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 8, 10, 12}

def Fin15AnchoredAtom3014 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 8, 10, 13}

def Fin15AnchoredAtom3019 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 8, 12, 13}

def Fin15AnchoredAtom3022 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 9, 10, 11}

def Fin15AnchoredAtom3023 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 9, 10, 12}

def Fin15AnchoredAtom3024 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 9, 10, 13}

def Fin15AnchoredAtom3025 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 9, 10, 14}

def Fin15AnchoredAtom3026 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 9, 11, 12}

def Fin15AnchoredAtom3029 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 9, 12, 13}

def Fin15AnchoredAtom3030 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 9, 12, 14}

def Fin15AnchoredAtom3031 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 9, 13, 14}

def Fin15AnchoredAtom3032 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 10, 11, 12}

def Fin15AnchoredAtom3035 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 10, 12, 13}

def Fin15AnchoredAtom3036 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 10, 12, 14}

def Fin15AnchoredAtom3037 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 10, 13, 14}

def Fin15AnchoredAtom3038 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 11, 12, 13}

def Fin15AnchoredAtom3041 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 2, 12, 13, 14}

def Fin15AnchoredAtom3042 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 6}

def Fin15AnchoredAtom3043 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 7}

def Fin15AnchoredAtom3044 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 8}

def Fin15AnchoredAtom3045 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 9}

def Fin15AnchoredAtom3046 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 10}

def Fin15AnchoredAtom3047 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 11}

def Fin15AnchoredAtom3048 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 12}

def Fin15AnchoredAtom3049 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 13}

def Fin15AnchoredAtom3050 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 14}

def Fin15AnchoredAtom3051 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 7}

def Fin15AnchoredAtom3052 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 8}

def Fin15AnchoredAtom3053 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 9}

def Fin15AnchoredAtom3054 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 10}

def Fin15AnchoredAtom3055 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 11}

def Fin15AnchoredAtom3056 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 12}

def Fin15AnchoredAtom3057 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 13}

def Fin15AnchoredAtom3058 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 14}

def Fin15AnchoredAtom3059 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 8}

def Fin15AnchoredAtom3060 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 9}

def Fin15AnchoredAtom3061 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 10}

def Fin15AnchoredAtom3062 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 11}

def Fin15AnchoredAtom3063 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 12}

def Fin15AnchoredAtom3064 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 13}

def Fin15AnchoredAtom3065 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 14}

def Fin15AnchoredAtom3066 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 9}

def Fin15AnchoredAtom3067 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 10}

def Fin15AnchoredAtom3069 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 12}

def Fin15AnchoredAtom3070 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 13}

def Fin15AnchoredAtom3071 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 14}

def Fin15AnchoredAtom3072 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 9, 10}

def Fin15AnchoredAtom3073 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 9, 11}

def Fin15AnchoredAtom3074 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 9, 12}

def Fin15AnchoredAtom3075 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 9, 13}

def Fin15AnchoredAtom3076 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 9, 14}

def Fin15AnchoredAtom3077 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 10, 11}

def Fin15AnchoredAtom3078 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 10, 12}

def Fin15AnchoredAtom3079 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 10, 13}

def Fin15AnchoredAtom3080 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 10, 14}

def Fin15AnchoredAtom3081 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 11, 12}

def Fin15AnchoredAtom3082 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 11, 13}

def Fin15AnchoredAtom3084 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 12, 13}

def Fin15AnchoredAtom3085 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 12, 14}

def Fin15AnchoredAtom3086 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 13, 14}

def Fin15AnchoredAtom3087 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 7}

def Fin15AnchoredAtom3088 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 8}

def Fin15AnchoredAtom3089 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 9}

def Fin15AnchoredAtom3090 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 10}

def Fin15AnchoredAtom3091 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 11}

def Fin15AnchoredAtom3092 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 12}

def Fin15AnchoredAtom3093 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 13}

def Fin15AnchoredAtom3094 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 14}

def Fin15AnchoredAtom3095 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 8}

def Fin15AnchoredAtom3096 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 9}

def Fin15AnchoredAtom3097 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 10}

def Fin15AnchoredAtom3098 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 11}

def Fin15AnchoredAtom3099 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 12}

def Fin15AnchoredAtom3100 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 13}

def Fin15AnchoredAtom3101 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 14}

def Fin15AnchoredAtom3102 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 9}

def Fin15AnchoredAtom3103 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 10}

def Fin15AnchoredAtom3105 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 12}

def Fin15AnchoredAtom3106 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 13}

def Fin15AnchoredAtom3107 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 14}

def Fin15AnchoredAtom3108 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 9, 10}

def Fin15AnchoredAtom3109 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 9, 11}

def Fin15AnchoredAtom3110 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 9, 12}

def Fin15AnchoredAtom3111 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 9, 13}

def Fin15AnchoredAtom3112 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 9, 14}

def Fin15AnchoredAtom3113 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 10, 11}

def Fin15AnchoredAtom3114 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 10, 12}

def Fin15AnchoredAtom3115 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 10, 13}

def Fin15AnchoredAtom3116 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 10, 14}

def Fin15AnchoredAtom3117 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 11, 12}

def Fin15AnchoredAtom3119 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 11, 14}

def Fin15AnchoredAtom3120 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 12, 13}

def Fin15AnchoredAtom3121 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 12, 14}

def Fin15AnchoredAtom3122 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 13, 14}

def Fin15AnchoredAtom3123 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 8}

def Fin15AnchoredAtom3124 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 9}

def Fin15AnchoredAtom3125 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 10}

def Fin15AnchoredAtom3126 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 11}

def Fin15AnchoredAtom3127 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 12}

def Fin15AnchoredAtom3128 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 13}

def Fin15AnchoredAtom3129 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 14}

def Fin15AnchoredAtom3130 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 9}

def Fin15AnchoredAtom3131 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 10}

def Fin15AnchoredAtom3133 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 12}

def Fin15AnchoredAtom3134 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 13}

def Fin15AnchoredAtom3135 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 14}

def Fin15AnchoredAtom3136 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 9, 10}

def Fin15AnchoredAtom3137 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 9, 11}

def Fin15AnchoredAtom3138 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 9, 12}

def Fin15AnchoredAtom3139 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 9, 13}

def Fin15AnchoredAtom3140 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 9, 14}

def Fin15AnchoredAtom3141 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 10, 11}

def Fin15AnchoredAtom3142 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 10, 12}

def Fin15AnchoredAtom3143 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 10, 13}

def Fin15AnchoredAtom3144 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 10, 14}

def Fin15AnchoredAtom3145 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 11, 12}

def Fin15AnchoredAtom3148 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 12, 13}

def Fin15AnchoredAtom3149 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 12, 14}

def Fin15AnchoredAtom3150 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 13, 14}

def Fin15AnchoredAtom3151 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 9}

def Fin15AnchoredAtom3152 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 10}

def Fin15AnchoredAtom3154 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 12}

def Fin15AnchoredAtom3155 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 13}

def Fin15AnchoredAtom3156 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 14}

def Fin15AnchoredAtom3157 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 9, 10}

def Fin15AnchoredAtom3158 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 9, 11}

def Fin15AnchoredAtom3159 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 9, 12}

def Fin15AnchoredAtom3160 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 9, 13}

def Fin15AnchoredAtom3161 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 9, 14}

def Fin15AnchoredAtom3162 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 10, 11}

def Fin15AnchoredAtom3163 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 10, 12}

def Fin15AnchoredAtom3164 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 10, 13}

def Fin15AnchoredAtom3165 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 10, 14}

def Fin15AnchoredAtom3166 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 11, 12}

def Fin15AnchoredAtom3167 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 11, 13}

def Fin15AnchoredAtom3168 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 11, 14}

def Fin15AnchoredAtom3169 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 12, 13}

def Fin15AnchoredAtom3170 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 12, 14}

def Fin15AnchoredAtom3171 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 13, 14}

def Fin15AnchoredAtom3172 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 9, 10}

def Fin15AnchoredAtom3174 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 9, 12}

def Fin15AnchoredAtom3175 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 9, 13}

def Fin15AnchoredAtom3176 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 9, 14}

def Fin15AnchoredAtom3178 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 10, 12}

def Fin15AnchoredAtom3179 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 10, 13}

def Fin15AnchoredAtom3180 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 10, 14}

def Fin15AnchoredAtom3184 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 12, 13}

def Fin15AnchoredAtom3185 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 12, 14}

def Fin15AnchoredAtom3186 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 13, 14}

def Fin15AnchoredAtom3187 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 9, 10, 11}

def Fin15AnchoredAtom3188 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 9, 10, 12}

def Fin15AnchoredAtom3189 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 9, 10, 13}

def Fin15AnchoredAtom3190 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 9, 10, 14}

def Fin15AnchoredAtom3191 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 9, 11, 12}

def Fin15AnchoredAtom3192 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 9, 11, 13}

def Fin15AnchoredAtom3193 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 9, 11, 14}

def Fin15AnchoredAtom3194 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 9, 12, 13}

def Fin15AnchoredAtom3195 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 9, 12, 14}

def Fin15AnchoredAtom3196 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 9, 13, 14}

def Fin15AnchoredAtom3197 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 10, 11, 12}

def Fin15AnchoredAtom3198 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 10, 11, 13}

def Fin15AnchoredAtom3199 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 10, 11, 14}

def Fin15AnchoredAtom3200 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 10, 12, 13}

def Fin15AnchoredAtom3201 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 10, 12, 14}

def Fin15AnchoredAtom3202 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 10, 13, 14}

def Fin15AnchoredAtom3203 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 11, 12, 13}

def Fin15AnchoredAtom3204 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 11, 12, 14}

def Fin15AnchoredAtom3206 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 3, 12, 13, 14}

def Fin15AnchoredAtom3207 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 7}

def Fin15AnchoredAtom3208 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 8}

def Fin15AnchoredAtom3209 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 9}

def Fin15AnchoredAtom3210 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 10}

def Fin15AnchoredAtom3211 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 11}

def Fin15AnchoredAtom3212 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 12}

def Fin15AnchoredAtom3213 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 13}

def Fin15AnchoredAtom3214 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 14}

def Fin15AnchoredAtom3215 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 8}

def Fin15AnchoredAtom3216 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 9}

def Fin15AnchoredAtom3217 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 10}

def Fin15AnchoredAtom3218 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 11}

def Fin15AnchoredAtom3219 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 12}

def Fin15AnchoredAtom3220 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 13}

def Fin15AnchoredAtom3221 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 14}

def Fin15AnchoredAtom3222 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 9}

def Fin15AnchoredAtom3223 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 10}

def Fin15AnchoredAtom3225 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 12}

def Fin15AnchoredAtom3226 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 13}

def Fin15AnchoredAtom3227 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 14}

def Fin15AnchoredAtom3228 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 9, 10}

def Fin15AnchoredAtom3229 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 9, 11}

def Fin15AnchoredAtom3230 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 9, 12}

def Fin15AnchoredAtom3231 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 9, 13}

def Fin15AnchoredAtom3232 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 9, 14}

def Fin15AnchoredAtom3233 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 10, 11}

def Fin15AnchoredAtom3234 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 10, 12}

def Fin15AnchoredAtom3235 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 10, 13}

def Fin15AnchoredAtom3236 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 10, 14}

def Fin15AnchoredAtom3237 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 11, 12}

def Fin15AnchoredAtom3238 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 11, 13}

def Fin15AnchoredAtom3239 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 11, 14}

def Fin15AnchoredAtom3240 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 12, 13}

def Fin15AnchoredAtom3241 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 12, 14}

def Fin15AnchoredAtom3242 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 13, 14}

def Fin15AnchoredAtom3243 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 8}

def Fin15AnchoredAtom3244 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 9}

def Fin15AnchoredAtom3245 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 10}

def Fin15AnchoredAtom3246 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 11}

def Fin15AnchoredAtom3247 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 12}

def Fin15AnchoredAtom3248 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 13}

def Fin15AnchoredAtom3249 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 14}

def Fin15AnchoredAtom3250 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 9}

def Fin15AnchoredAtom3251 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 10}

def Fin15AnchoredAtom3253 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 12}

def Fin15AnchoredAtom3254 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 13}

def Fin15AnchoredAtom3255 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 14}

def Fin15AnchoredAtom3256 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 9, 10}

def Fin15AnchoredAtom3257 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 9, 11}

def Fin15AnchoredAtom3258 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 9, 12}

def Fin15AnchoredAtom3259 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 9, 13}

def Fin15AnchoredAtom3260 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 9, 14}

def Fin15AnchoredAtom3261 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 10, 11}

def Fin15AnchoredAtom3262 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 10, 12}

def Fin15AnchoredAtom3263 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 10, 13}

def Fin15AnchoredAtom3264 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 10, 14}

def Fin15AnchoredAtom3265 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 11, 12}

def Fin15AnchoredAtom3266 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 11, 13}

def Fin15AnchoredAtom3268 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 12, 13}

def Fin15AnchoredAtom3269 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 12, 14}

def Fin15AnchoredAtom3270 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 13, 14}

def Fin15AnchoredAtom3271 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 9}

def Fin15AnchoredAtom3272 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 10}

def Fin15AnchoredAtom3274 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 12}

def Fin15AnchoredAtom3275 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 13}

def Fin15AnchoredAtom3276 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 14}

def Fin15AnchoredAtom3277 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 9, 10}

def Fin15AnchoredAtom3278 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 9, 11}

def Fin15AnchoredAtom3279 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 9, 12}

def Fin15AnchoredAtom3280 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 9, 13}

def Fin15AnchoredAtom3281 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 9, 14}

def Fin15AnchoredAtom3282 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 10, 11}

def Fin15AnchoredAtom3283 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 10, 12}

def Fin15AnchoredAtom3284 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 10, 13}

def Fin15AnchoredAtom3285 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 10, 14}

def Fin15AnchoredAtom3286 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 11, 12}

def Fin15AnchoredAtom3287 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 11, 13}

def Fin15AnchoredAtom3288 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 11, 14}

def Fin15AnchoredAtom3289 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 12, 13}

def Fin15AnchoredAtom3290 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 12, 14}

def Fin15AnchoredAtom3291 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 13, 14}

def Fin15AnchoredAtom3292 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 9, 10}

def Fin15AnchoredAtom3294 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 9, 12}

def Fin15AnchoredAtom3295 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 9, 13}

def Fin15AnchoredAtom3296 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 9, 14}

def Fin15AnchoredAtom3298 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 10, 12}

def Fin15AnchoredAtom3299 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 10, 13}

def Fin15AnchoredAtom3300 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 10, 14}

def Fin15AnchoredAtom3304 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 12, 13}

def Fin15AnchoredAtom3305 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 12, 14}

def Fin15AnchoredAtom3306 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 13, 14}

def Fin15AnchoredAtom3307 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 9, 10, 11}

def Fin15AnchoredAtom3308 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 9, 10, 12}

def Fin15AnchoredAtom3309 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 9, 10, 13}

def Fin15AnchoredAtom3310 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 9, 10, 14}

def Fin15AnchoredAtom3311 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 9, 11, 12}

def Fin15AnchoredAtom3312 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 9, 11, 13}

def Fin15AnchoredAtom3313 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 9, 11, 14}

def Fin15AnchoredAtom3314 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 9, 12, 13}

def Fin15AnchoredAtom3315 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 9, 12, 14}

def Fin15AnchoredAtom3316 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 9, 13, 14}

def Fin15AnchoredAtom3317 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 10, 11, 12}

def Fin15AnchoredAtom3318 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 10, 11, 13}

def Fin15AnchoredAtom3319 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 10, 11, 14}

def Fin15AnchoredAtom3320 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 10, 12, 13}

def Fin15AnchoredAtom3321 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 10, 12, 14}

def Fin15AnchoredAtom3322 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 10, 13, 14}

def Fin15AnchoredAtom3323 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 11, 12, 13}

def Fin15AnchoredAtom3324 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 11, 12, 14}

def Fin15AnchoredAtom3326 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 4, 12, 13, 14}

def Fin15AnchoredAtom3327 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 8}

def Fin15AnchoredAtom3328 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 9}

def Fin15AnchoredAtom3329 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 10}

def Fin15AnchoredAtom3331 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 12}

def Fin15AnchoredAtom3332 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 13}

def Fin15AnchoredAtom3333 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 14}

def Fin15AnchoredAtom3334 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 9}

def Fin15AnchoredAtom3335 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 10}

def Fin15AnchoredAtom3337 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 12}

def Fin15AnchoredAtom3338 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 13}

def Fin15AnchoredAtom3339 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 14}

def Fin15AnchoredAtom3340 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 9, 10}

def Fin15AnchoredAtom3341 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 9, 11}

def Fin15AnchoredAtom3342 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 9, 12}

def Fin15AnchoredAtom3343 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 9, 13}

def Fin15AnchoredAtom3344 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 9, 14}

def Fin15AnchoredAtom3345 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 10, 11}

def Fin15AnchoredAtom3346 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 10, 12}

def Fin15AnchoredAtom3347 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 10, 13}

def Fin15AnchoredAtom3348 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 10, 14}

def Fin15AnchoredAtom3349 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 11, 12}

def Fin15AnchoredAtom3352 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 12, 13}

def Fin15AnchoredAtom3353 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 12, 14}

def Fin15AnchoredAtom3354 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 13, 14}

def Fin15AnchoredAtom3355 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 9}

def Fin15AnchoredAtom3356 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 10}

def Fin15AnchoredAtom3358 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 12}

def Fin15AnchoredAtom3359 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 13}

def Fin15AnchoredAtom3360 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 14}

def Fin15AnchoredAtom3361 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 9, 10}

def Fin15AnchoredAtom3362 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 9, 11}

def Fin15AnchoredAtom3363 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 9, 12}

def Fin15AnchoredAtom3364 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 9, 13}

def Fin15AnchoredAtom3365 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 9, 14}

def Fin15AnchoredAtom3366 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 10, 11}

def Fin15AnchoredAtom3367 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 10, 12}

def Fin15AnchoredAtom3368 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 10, 13}

def Fin15AnchoredAtom3369 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 10, 14}

def Fin15AnchoredAtom3370 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 11, 12}

def Fin15AnchoredAtom3371 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 11, 13}

def Fin15AnchoredAtom3372 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 11, 14}

def Fin15AnchoredAtom3373 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 12, 13}

def Fin15AnchoredAtom3374 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 12, 14}

def Fin15AnchoredAtom3375 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 13, 14}

def Fin15AnchoredAtom3376 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 9, 10}

def Fin15AnchoredAtom3378 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 9, 12}

def Fin15AnchoredAtom3379 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 9, 13}

def Fin15AnchoredAtom3380 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 9, 14}

def Fin15AnchoredAtom3382 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 10, 12}

def Fin15AnchoredAtom3383 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 10, 13}

def Fin15AnchoredAtom3384 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 10, 14}

def Fin15AnchoredAtom3388 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 12, 13}

def Fin15AnchoredAtom3389 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 12, 14}

def Fin15AnchoredAtom3390 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 13, 14}

def Fin15AnchoredAtom3391 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 9, 10, 11}

def Fin15AnchoredAtom3392 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 9, 10, 12}

def Fin15AnchoredAtom3393 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 9, 10, 13}

def Fin15AnchoredAtom3394 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 9, 10, 14}

def Fin15AnchoredAtom3395 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 9, 11, 12}

def Fin15AnchoredAtom3396 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 9, 11, 13}

def Fin15AnchoredAtom3397 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 9, 11, 14}

def Fin15AnchoredAtom3398 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 9, 12, 13}

def Fin15AnchoredAtom3399 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 9, 12, 14}

def Fin15AnchoredAtom3400 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 9, 13, 14}

def Fin15AnchoredAtom3401 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 10, 11, 12}

def Fin15AnchoredAtom3402 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 10, 11, 13}

def Fin15AnchoredAtom3403 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 10, 11, 14}

def Fin15AnchoredAtom3404 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 10, 12, 13}

def Fin15AnchoredAtom3405 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 10, 12, 14}

def Fin15AnchoredAtom3406 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 10, 13, 14}

def Fin15AnchoredAtom3407 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 11, 12, 13}

def Fin15AnchoredAtom3408 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 11, 12, 14}

def Fin15AnchoredAtom3410 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 5, 12, 13, 14}

def Fin15AnchoredAtom3411 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 9}

def Fin15AnchoredAtom3412 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 10}

def Fin15AnchoredAtom3414 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 12}

def Fin15AnchoredAtom3415 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 13}

def Fin15AnchoredAtom3416 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 14}

def Fin15AnchoredAtom3417 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 9, 10}

def Fin15AnchoredAtom3418 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 9, 11}

def Fin15AnchoredAtom3419 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 9, 12}

def Fin15AnchoredAtom3420 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 9, 13}

def Fin15AnchoredAtom3421 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 9, 14}

def Fin15AnchoredAtom3422 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 10, 11}

def Fin15AnchoredAtom3423 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 10, 12}

def Fin15AnchoredAtom3424 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 10, 13}

def Fin15AnchoredAtom3425 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 10, 14}

def Fin15AnchoredAtom3426 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 11, 12}

def Fin15AnchoredAtom3428 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 11, 14}

def Fin15AnchoredAtom3429 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 12, 13}

def Fin15AnchoredAtom3430 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 12, 14}

def Fin15AnchoredAtom3431 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 13, 14}

def Fin15AnchoredAtom3432 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 9, 10}

def Fin15AnchoredAtom3434 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 9, 12}

def Fin15AnchoredAtom3435 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 9, 13}

def Fin15AnchoredAtom3436 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 9, 14}

def Fin15AnchoredAtom3438 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 10, 12}

def Fin15AnchoredAtom3439 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 10, 13}

def Fin15AnchoredAtom3440 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 10, 14}

def Fin15AnchoredAtom3444 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 12, 13}

def Fin15AnchoredAtom3445 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 12, 14}

def Fin15AnchoredAtom3446 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 13, 14}

def Fin15AnchoredAtom3447 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 9, 10, 11}

def Fin15AnchoredAtom3448 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 9, 10, 12}

def Fin15AnchoredAtom3449 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 9, 10, 13}

def Fin15AnchoredAtom3450 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 9, 10, 14}

def Fin15AnchoredAtom3451 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 9, 11, 12}

def Fin15AnchoredAtom3452 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 9, 11, 13}

def Fin15AnchoredAtom3453 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 9, 11, 14}

def Fin15AnchoredAtom3454 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 9, 12, 13}

def Fin15AnchoredAtom3455 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 9, 12, 14}

def Fin15AnchoredAtom3456 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 9, 13, 14}

def Fin15AnchoredAtom3457 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 10, 11, 12}

def Fin15AnchoredAtom3458 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 10, 11, 13}

def Fin15AnchoredAtom3459 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 10, 11, 14}

def Fin15AnchoredAtom3460 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 10, 12, 13}

def Fin15AnchoredAtom3461 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 10, 12, 14}

def Fin15AnchoredAtom3462 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 10, 13, 14}

def Fin15AnchoredAtom3463 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 11, 12, 13}

def Fin15AnchoredAtom3464 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 11, 12, 14}

def Fin15AnchoredAtom3466 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 6, 12, 13, 14}

def Fin15AnchoredAtom3467 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 9, 10}

def Fin15AnchoredAtom3469 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 9, 12}

def Fin15AnchoredAtom3470 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 9, 13}

def Fin15AnchoredAtom3471 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 9, 14}

def Fin15AnchoredAtom3473 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 10, 12}

def Fin15AnchoredAtom3474 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 10, 13}

def Fin15AnchoredAtom3475 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 10, 14}

def Fin15AnchoredAtom3479 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 12, 13}

def Fin15AnchoredAtom3480 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 12, 14}

def Fin15AnchoredAtom3481 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 13, 14}

def Fin15AnchoredAtom3482 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 9, 10, 11}

def Fin15AnchoredAtom3483 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 9, 10, 12}

def Fin15AnchoredAtom3484 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 9, 10, 13}

def Fin15AnchoredAtom3485 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 9, 10, 14}

def Fin15AnchoredAtom3486 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 9, 11, 12}

def Fin15AnchoredAtom3487 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 9, 11, 13}

def Fin15AnchoredAtom3488 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 9, 11, 14}

def Fin15AnchoredAtom3489 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 9, 12, 13}

def Fin15AnchoredAtom3490 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 9, 12, 14}

def Fin15AnchoredAtom3491 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 9, 13, 14}

def Fin15AnchoredAtom3492 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 10, 11, 12}

def Fin15AnchoredAtom3493 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 10, 11, 13}

def Fin15AnchoredAtom3494 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 10, 11, 14}

def Fin15AnchoredAtom3495 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 10, 12, 13}

def Fin15AnchoredAtom3496 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 10, 12, 14}

def Fin15AnchoredAtom3497 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 10, 13, 14}

def Fin15AnchoredAtom3498 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 11, 12, 13}

def Fin15AnchoredAtom3499 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 11, 12, 14}

def Fin15AnchoredAtom3500 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 11, 13, 14}

def Fin15AnchoredAtom3501 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 7, 12, 13, 14}

def Fin15AnchoredAtom3503 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 8, 9, 10, 12}

def Fin15AnchoredAtom3504 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 8, 9, 10, 13}

def Fin15AnchoredAtom3505 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 8, 9, 10, 14}

def Fin15AnchoredAtom3509 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 8, 9, 12, 13}

def Fin15AnchoredAtom3510 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 8, 9, 12, 14}

def Fin15AnchoredAtom3511 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 8, 9, 13, 14}

def Fin15AnchoredAtom3515 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 8, 10, 12, 13}

def Fin15AnchoredAtom3516 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 8, 10, 12, 14}

def Fin15AnchoredAtom3517 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 8, 10, 13, 14}

def Fin15AnchoredAtom3521 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 8, 12, 13, 14}

def Fin15AnchoredAtom3522 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 9, 10, 11, 12}

def Fin15AnchoredAtom3523 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 9, 10, 11, 13}

def Fin15AnchoredAtom3524 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 9, 10, 11, 14}

def Fin15AnchoredAtom3525 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 9, 10, 12, 13}

def Fin15AnchoredAtom3526 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 9, 10, 12, 14}

def Fin15AnchoredAtom3527 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 9, 10, 13, 14}

def Fin15AnchoredAtom3528 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 9, 11, 12, 13}

def Fin15AnchoredAtom3529 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 9, 11, 12, 14}

def Fin15AnchoredAtom3531 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 9, 12, 13, 14}

def Fin15AnchoredAtom3532 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 10, 11, 12, 13}

def Fin15AnchoredAtom3533 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 10, 11, 12, 14}

def Fin15AnchoredAtom3534 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 10, 11, 13, 14}

def Fin15AnchoredAtom3535 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 10, 12, 13, 14}

def Fin15AnchoredAtom3536 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {1, 11, 12, 13, 14}

def Fin15AnchoredAtom3537 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 6}

def Fin15AnchoredAtom3538 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 7}

def Fin15AnchoredAtom3539 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 8}

def Fin15AnchoredAtom3540 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 9}

def Fin15AnchoredAtom3541 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 10}

def Fin15AnchoredAtom3542 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 11}

def Fin15AnchoredAtom3543 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 12}

def Fin15AnchoredAtom3544 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 13}

def Fin15AnchoredAtom3545 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 14}

def Fin15AnchoredAtom3546 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 7}

def Fin15AnchoredAtom3547 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 8}

def Fin15AnchoredAtom3548 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 9}

def Fin15AnchoredAtom3549 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 10}

def Fin15AnchoredAtom3550 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 11}

def Fin15AnchoredAtom3551 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 12}

def Fin15AnchoredAtom3552 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 13}

def Fin15AnchoredAtom3553 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 14}

def Fin15AnchoredAtom3554 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 8}

def Fin15AnchoredAtom3555 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 9}

def Fin15AnchoredAtom3556 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 10}

def Fin15AnchoredAtom3557 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 11}

def Fin15AnchoredAtom3558 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 12}

def Fin15AnchoredAtom3559 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 13}

def Fin15AnchoredAtom3560 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 14}

def Fin15AnchoredAtom3561 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 9}

def Fin15AnchoredAtom3562 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 10}

def Fin15AnchoredAtom3565 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 13}

def Fin15AnchoredAtom3566 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 14}

def Fin15AnchoredAtom3567 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 10}

def Fin15AnchoredAtom3568 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 11}

def Fin15AnchoredAtom3569 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 12}

def Fin15AnchoredAtom3570 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 13}

def Fin15AnchoredAtom3571 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 14}

def Fin15AnchoredAtom3572 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 10, 11}

def Fin15AnchoredAtom3573 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 10, 12}

def Fin15AnchoredAtom3574 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 10, 13}

def Fin15AnchoredAtom3575 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 10, 14}

def Fin15AnchoredAtom3576 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 11, 12}

def Fin15AnchoredAtom3577 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 11, 13}

def Fin15AnchoredAtom3578 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 11, 14}

def Fin15AnchoredAtom3579 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 12, 13}

def Fin15AnchoredAtom3580 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 12, 14}

def Fin15AnchoredAtom3581 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 13, 14}

def Fin15AnchoredAtom3582 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 7}

def Fin15AnchoredAtom3583 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 8}

def Fin15AnchoredAtom3584 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 9}

def Fin15AnchoredAtom3585 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 10}

def Fin15AnchoredAtom3586 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 11}

def Fin15AnchoredAtom3587 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 12}

def Fin15AnchoredAtom3588 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 13}

def Fin15AnchoredAtom3589 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 14}

def Fin15AnchoredAtom3590 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 8}

def Fin15AnchoredAtom3591 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 9}

def Fin15AnchoredAtom3592 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 10}

def Fin15AnchoredAtom3593 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 11}

def Fin15AnchoredAtom3594 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 12}

def Fin15AnchoredAtom3595 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 13}

def Fin15AnchoredAtom3596 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 14}

def Fin15AnchoredAtom3597 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 9}

def Fin15AnchoredAtom3598 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 10}

def Fin15AnchoredAtom3600 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 12}

def Fin15AnchoredAtom3601 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 13}

def Fin15AnchoredAtom3602 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 14}

def Fin15AnchoredAtom3603 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 10}

def Fin15AnchoredAtom3604 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 11}

def Fin15AnchoredAtom3605 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 12}

def Fin15AnchoredAtom3606 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 13}

def Fin15AnchoredAtom3607 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 14}

def Fin15AnchoredAtom3608 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 10, 11}

def Fin15AnchoredAtom3609 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 10, 12}

def Fin15AnchoredAtom3610 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 10, 13}

def Fin15AnchoredAtom3611 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 10, 14}

def Fin15AnchoredAtom3612 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 11, 12}

def Fin15AnchoredAtom3613 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 11, 13}

def Fin15AnchoredAtom3614 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 11, 14}

def Fin15AnchoredAtom3615 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 12, 13}

def Fin15AnchoredAtom3616 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 12, 14}

def Fin15AnchoredAtom3617 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 13, 14}

def Fin15AnchoredAtom3618 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 8}

def Fin15AnchoredAtom3619 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 9}

def Fin15AnchoredAtom3620 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 10}

def Fin15AnchoredAtom3621 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 11}

def Fin15AnchoredAtom3622 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 12}

def Fin15AnchoredAtom3623 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 13}

def Fin15AnchoredAtom3624 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 14}

def Fin15AnchoredAtom3625 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 9}

def Fin15AnchoredAtom3626 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 10}

def Fin15AnchoredAtom3628 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 12}

def Fin15AnchoredAtom3629 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 13}

def Fin15AnchoredAtom3630 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 14}

def Fin15AnchoredAtom3631 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 10}

def Fin15AnchoredAtom3632 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 11}

def Fin15AnchoredAtom3633 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 12}

def Fin15AnchoredAtom3634 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 13}

def Fin15AnchoredAtom3635 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 14}

def Fin15AnchoredAtom3636 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 10, 11}

def Fin15AnchoredAtom3637 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 10, 12}

def Fin15AnchoredAtom3638 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 10, 13}

def Fin15AnchoredAtom3639 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 10, 14}

def Fin15AnchoredAtom3640 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 11, 12}

def Fin15AnchoredAtom3641 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 11, 13}

def Fin15AnchoredAtom3642 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 11, 14}

def Fin15AnchoredAtom3643 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 12, 13}

def Fin15AnchoredAtom3644 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 12, 14}

def Fin15AnchoredAtom3645 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 13, 14}

def Fin15AnchoredAtom3647 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 10}

def Fin15AnchoredAtom3650 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 13}

def Fin15AnchoredAtom3651 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 14}

def Fin15AnchoredAtom3652 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 10}

def Fin15AnchoredAtom3653 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 11}

def Fin15AnchoredAtom3654 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 12}

def Fin15AnchoredAtom3655 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 13}

def Fin15AnchoredAtom3656 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 14}

def Fin15AnchoredAtom3657 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 10, 11}

def Fin15AnchoredAtom3658 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 10, 12}

def Fin15AnchoredAtom3659 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 10, 13}

def Fin15AnchoredAtom3660 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 10, 14}

def Fin15AnchoredAtom3661 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 11, 12}

def Fin15AnchoredAtom3663 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 11, 14}

def Fin15AnchoredAtom3664 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 12, 13}

def Fin15AnchoredAtom3665 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 12, 14}

def Fin15AnchoredAtom3666 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 13, 14}

def Fin15AnchoredAtom3667 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 9, 10}

def Fin15AnchoredAtom3673 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 10, 12}

def Fin15AnchoredAtom3674 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 10, 13}

def Fin15AnchoredAtom3679 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 12, 13}

def Fin15AnchoredAtom3682 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 10, 11}

def Fin15AnchoredAtom3683 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 10, 12}

def Fin15AnchoredAtom3684 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 10, 13}

def Fin15AnchoredAtom3685 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 10, 14}

def Fin15AnchoredAtom3686 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 11, 12}

def Fin15AnchoredAtom3687 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 11, 13}

def Fin15AnchoredAtom3688 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 11, 14}

def Fin15AnchoredAtom3689 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 12, 13}

def Fin15AnchoredAtom3690 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 12, 14}

def Fin15AnchoredAtom3691 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 13, 14}

def Fin15AnchoredAtom3692 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 10, 11, 12}

def Fin15AnchoredAtom3693 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 10, 11, 13}

def Fin15AnchoredAtom3694 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 10, 11, 14}

def Fin15AnchoredAtom3695 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 10, 12, 13}

def Fin15AnchoredAtom3696 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 10, 12, 14}

def Fin15AnchoredAtom3697 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 10, 13, 14}

def Fin15AnchoredAtom3698 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 11, 12, 13}

def Fin15AnchoredAtom3699 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 11, 12, 14}

def Fin15AnchoredAtom3701 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 3, 12, 13, 14}

def Fin15AnchoredAtom3702 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 7}

def Fin15AnchoredAtom3703 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 8}

def Fin15AnchoredAtom3704 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 9}

def Fin15AnchoredAtom3705 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 10}

def Fin15AnchoredAtom3706 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 11}

def Fin15AnchoredAtom3707 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 12}

def Fin15AnchoredAtom3708 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 13}

def Fin15AnchoredAtom3709 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 14}

def Fin15AnchoredAtom3711 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 9}

def Fin15AnchoredAtom3712 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 10}

def Fin15AnchoredAtom3713 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 11}

def Fin15AnchoredAtom3714 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 12}

def Fin15AnchoredAtom3715 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 13}

def Fin15AnchoredAtom3716 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 14}

def Fin15AnchoredAtom3721 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 13}

def Fin15AnchoredAtom3723 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 10}

def Fin15AnchoredAtom3724 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 11}

def Fin15AnchoredAtom3725 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 12}

def Fin15AnchoredAtom3726 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 13}

def Fin15AnchoredAtom3727 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 14}

def Fin15AnchoredAtom3728 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 10, 11}

def Fin15AnchoredAtom3729 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 10, 12}

def Fin15AnchoredAtom3730 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 10, 13}

def Fin15AnchoredAtom3731 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 10, 14}

def Fin15AnchoredAtom3732 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 11, 12}

def Fin15AnchoredAtom3733 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 11, 13}

def Fin15AnchoredAtom3734 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 11, 14}

def Fin15AnchoredAtom3735 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 12, 13}

def Fin15AnchoredAtom3736 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 12, 14}

def Fin15AnchoredAtom3737 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 13, 14}

def Fin15AnchoredAtom3738 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 8}

def Fin15AnchoredAtom3739 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 9}

def Fin15AnchoredAtom3740 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 10}

def Fin15AnchoredAtom3741 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 11}

def Fin15AnchoredAtom3742 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 12}

def Fin15AnchoredAtom3743 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 13}

def Fin15AnchoredAtom3744 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 14}

def Fin15AnchoredAtom3745 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 9}

def Fin15AnchoredAtom3746 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 10}

def Fin15AnchoredAtom3748 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 12}

def Fin15AnchoredAtom3749 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 13}

def Fin15AnchoredAtom3750 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 14}

def Fin15AnchoredAtom3751 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 10}

def Fin15AnchoredAtom3752 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 11}

def Fin15AnchoredAtom3753 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 12}

def Fin15AnchoredAtom3754 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 13}

def Fin15AnchoredAtom3755 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 14}

def Fin15AnchoredAtom3756 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 10, 11}

def Fin15AnchoredAtom3757 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 10, 12}

def Fin15AnchoredAtom3758 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 10, 13}

def Fin15AnchoredAtom3759 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 10, 14}

def Fin15AnchoredAtom3760 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 11, 12}

def Fin15AnchoredAtom3761 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 11, 13}

def Fin15AnchoredAtom3762 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 11, 14}

def Fin15AnchoredAtom3763 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 12, 13}

def Fin15AnchoredAtom3764 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 12, 14}

def Fin15AnchoredAtom3765 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 13, 14}

def Fin15AnchoredAtom3766 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 9}

def Fin15AnchoredAtom3767 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 10}

def Fin15AnchoredAtom3769 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 12}

def Fin15AnchoredAtom3771 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 14}

def Fin15AnchoredAtom3772 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 10}

def Fin15AnchoredAtom3773 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 11}

def Fin15AnchoredAtom3774 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 12}

def Fin15AnchoredAtom3775 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 13}

def Fin15AnchoredAtom3776 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 14}

def Fin15AnchoredAtom3777 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 10, 11}

def Fin15AnchoredAtom3778 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 10, 12}

def Fin15AnchoredAtom3779 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 10, 13}

def Fin15AnchoredAtom3780 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 10, 14}

def Fin15AnchoredAtom3781 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 11, 12}

def Fin15AnchoredAtom3782 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 11, 13}

def Fin15AnchoredAtom3783 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 11, 14}

def Fin15AnchoredAtom3784 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 12, 13}

def Fin15AnchoredAtom3785 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 12, 14}

def Fin15AnchoredAtom3786 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 13, 14}

def Fin15AnchoredAtom3787 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 9, 10}

def Fin15AnchoredAtom3789 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 9, 12}

def Fin15AnchoredAtom3791 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 9, 14}

def Fin15AnchoredAtom3793 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 10, 12}

def Fin15AnchoredAtom3794 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 10, 13}

def Fin15AnchoredAtom3795 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 10, 14}

def Fin15AnchoredAtom3799 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 12, 13}

def Fin15AnchoredAtom3800 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 12, 14}

def Fin15AnchoredAtom3801 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 13, 14}

def Fin15AnchoredAtom3802 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 10, 11}

def Fin15AnchoredAtom3803 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 10, 12}

def Fin15AnchoredAtom3804 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 10, 13}

def Fin15AnchoredAtom3805 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 10, 14}

def Fin15AnchoredAtom3806 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 11, 12}

def Fin15AnchoredAtom3807 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 11, 13}

def Fin15AnchoredAtom3808 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 11, 14}

def Fin15AnchoredAtom3809 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 12, 13}

def Fin15AnchoredAtom3810 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 12, 14}

def Fin15AnchoredAtom3811 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 13, 14}

def Fin15AnchoredAtom3812 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 10, 11, 12}

def Fin15AnchoredAtom3813 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 10, 11, 13}

def Fin15AnchoredAtom3814 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 10, 11, 14}

def Fin15AnchoredAtom3815 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 10, 12, 13}

def Fin15AnchoredAtom3816 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 10, 12, 14}

def Fin15AnchoredAtom3817 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 10, 13, 14}

def Fin15AnchoredAtom3818 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 11, 12, 13}

def Fin15AnchoredAtom3819 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 11, 12, 14}

def Fin15AnchoredAtom3821 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 4, 12, 13, 14}

def Fin15AnchoredAtom3823 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 9}

def Fin15AnchoredAtom3824 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 10}

def Fin15AnchoredAtom3825 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 11}

def Fin15AnchoredAtom3826 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 12}

def Fin15AnchoredAtom3827 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 13}

def Fin15AnchoredAtom3828 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 14}

def Fin15AnchoredAtom3830 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 10}

def Fin15AnchoredAtom3833 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 13}

def Fin15AnchoredAtom3835 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 10}

def Fin15AnchoredAtom3836 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 11}

def Fin15AnchoredAtom3837 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 12}

def Fin15AnchoredAtom3838 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 13}

def Fin15AnchoredAtom3839 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 14}

def Fin15AnchoredAtom3840 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 10, 11}

def Fin15AnchoredAtom3841 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 10, 12}

def Fin15AnchoredAtom3842 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 10, 13}

def Fin15AnchoredAtom3843 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 10, 14}

def Fin15AnchoredAtom3844 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 11, 12}

def Fin15AnchoredAtom3845 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 11, 13}

def Fin15AnchoredAtom3846 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 11, 14}

def Fin15AnchoredAtom3847 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 12, 13}

def Fin15AnchoredAtom3848 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 12, 14}

def Fin15AnchoredAtom3849 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 13, 14}

def Fin15AnchoredAtom3851 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 10}

def Fin15AnchoredAtom3854 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 13}

def Fin15AnchoredAtom3856 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 10}

def Fin15AnchoredAtom3857 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 11}

def Fin15AnchoredAtom3858 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 12}

def Fin15AnchoredAtom3859 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 13}

def Fin15AnchoredAtom3860 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 14}

def Fin15AnchoredAtom3861 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 10, 11}

def Fin15AnchoredAtom3862 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 10, 12}

def Fin15AnchoredAtom3863 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 10, 13}

def Fin15AnchoredAtom3864 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 10, 14}

def Fin15AnchoredAtom3865 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 11, 12}

def Fin15AnchoredAtom3866 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 11, 13}

def Fin15AnchoredAtom3867 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 11, 14}

def Fin15AnchoredAtom3868 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 12, 13}

def Fin15AnchoredAtom3869 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 12, 14}

def Fin15AnchoredAtom3870 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 13, 14}

def Fin15AnchoredAtom3877 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 10, 12}

def Fin15AnchoredAtom3878 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 10, 13}

def Fin15AnchoredAtom3883 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 12, 13}

def Fin15AnchoredAtom3886 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 10, 11}

def Fin15AnchoredAtom3887 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 10, 12}

def Fin15AnchoredAtom3888 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 10, 13}

def Fin15AnchoredAtom3889 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 10, 14}

def Fin15AnchoredAtom3890 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 11, 12}

def Fin15AnchoredAtom3891 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 11, 13}

def Fin15AnchoredAtom3892 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 11, 14}

def Fin15AnchoredAtom3893 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 12, 13}

def Fin15AnchoredAtom3894 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 12, 14}

def Fin15AnchoredAtom3895 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 13, 14}

def Fin15AnchoredAtom3896 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 10, 11, 12}

def Fin15AnchoredAtom3897 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 10, 11, 13}

def Fin15AnchoredAtom3898 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 10, 11, 14}

def Fin15AnchoredAtom3899 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 10, 12, 13}

def Fin15AnchoredAtom3900 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 10, 12, 14}

def Fin15AnchoredAtom3901 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 10, 13, 14}

def Fin15AnchoredAtom3902 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 11, 12, 13}

def Fin15AnchoredAtom3903 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 11, 12, 14}

def Fin15AnchoredAtom3904 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 11, 13, 14}

def Fin15AnchoredAtom3905 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 5, 12, 13, 14}

def Fin15AnchoredAtom3906 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 9}

def Fin15AnchoredAtom3907 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 10}

def Fin15AnchoredAtom3911 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 14}

def Fin15AnchoredAtom3912 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 10}

def Fin15AnchoredAtom3913 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 11}

def Fin15AnchoredAtom3914 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 12}

def Fin15AnchoredAtom3915 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 13}

def Fin15AnchoredAtom3916 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 14}

def Fin15AnchoredAtom3917 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 10, 11}

def Fin15AnchoredAtom3918 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 10, 12}

def Fin15AnchoredAtom3919 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 10, 13}

def Fin15AnchoredAtom3920 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 10, 14}

def Fin15AnchoredAtom3921 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 11, 12}

def Fin15AnchoredAtom3922 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 11, 13}

def Fin15AnchoredAtom3923 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 11, 14}

def Fin15AnchoredAtom3924 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 12, 13}

def Fin15AnchoredAtom3925 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 12, 14}

def Fin15AnchoredAtom3926 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 13, 14}

def Fin15AnchoredAtom3927 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 9, 10}

def Fin15AnchoredAtom3933 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 10, 12}

def Fin15AnchoredAtom3934 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 10, 13}

def Fin15AnchoredAtom3935 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 10, 14}

def Fin15AnchoredAtom3939 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 12, 13}

def Fin15AnchoredAtom3940 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 12, 14}

def Fin15AnchoredAtom3941 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 13, 14}

def Fin15AnchoredAtom3942 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 10, 11}

def Fin15AnchoredAtom3943 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 10, 12}

def Fin15AnchoredAtom3944 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 10, 13}

def Fin15AnchoredAtom3945 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 10, 14}

def Fin15AnchoredAtom3946 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 11, 12}

def Fin15AnchoredAtom3947 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 11, 13}

def Fin15AnchoredAtom3948 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 11, 14}

def Fin15AnchoredAtom3949 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 12, 13}

def Fin15AnchoredAtom3950 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 12, 14}

def Fin15AnchoredAtom3951 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 13, 14}

def Fin15AnchoredAtom3952 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 10, 11, 12}

def Fin15AnchoredAtom3953 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 10, 11, 13}

def Fin15AnchoredAtom3954 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 10, 11, 14}

def Fin15AnchoredAtom3955 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 10, 12, 13}

def Fin15AnchoredAtom3956 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 10, 12, 14}

def Fin15AnchoredAtom3957 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 10, 13, 14}

def Fin15AnchoredAtom3958 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 11, 12, 13}

def Fin15AnchoredAtom3959 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 11, 12, 14}

def Fin15AnchoredAtom3961 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 6, 12, 13, 14}

def Fin15AnchoredAtom3962 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 9, 10}

def Fin15AnchoredAtom3964 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 9, 12}

def Fin15AnchoredAtom3966 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 9, 14}

def Fin15AnchoredAtom3969 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 10, 13}

def Fin15AnchoredAtom3975 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 12, 14}

def Fin15AnchoredAtom3977 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 10, 11}

def Fin15AnchoredAtom3978 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 10, 12}

def Fin15AnchoredAtom3979 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 10, 13}

def Fin15AnchoredAtom3980 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 10, 14}

def Fin15AnchoredAtom3981 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 11, 12}

def Fin15AnchoredAtom3982 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 11, 13}

def Fin15AnchoredAtom3983 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 11, 14}

def Fin15AnchoredAtom3984 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 12, 13}

def Fin15AnchoredAtom3985 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 12, 14}

def Fin15AnchoredAtom3986 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 13, 14}

def Fin15AnchoredAtom3987 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 10, 11, 12}

def Fin15AnchoredAtom3988 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 10, 11, 13}

def Fin15AnchoredAtom3989 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 10, 11, 14}

def Fin15AnchoredAtom3990 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 10, 12, 13}

def Fin15AnchoredAtom3991 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 10, 12, 14}

def Fin15AnchoredAtom3992 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 10, 13, 14}

def Fin15AnchoredAtom3993 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 11, 12, 13}

def Fin15AnchoredAtom3994 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 11, 12, 14}

def Fin15AnchoredAtom3995 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 11, 13, 14}

def Fin15AnchoredAtom3996 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 7, 12, 13, 14}

def Fin15AnchoredAtom3998 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 8, 9, 10, 12}

def Fin15AnchoredAtom4005 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 8, 9, 12, 14}

def Fin15AnchoredAtom4010 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 8, 10, 12, 13}

def Fin15AnchoredAtom4011 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 8, 10, 12, 14}

def Fin15AnchoredAtom4012 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 8, 10, 13, 14}

def Fin15AnchoredAtom4016 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 8, 12, 13, 14}

def Fin15AnchoredAtom4017 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 9, 10, 11, 12}

def Fin15AnchoredAtom4018 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 9, 10, 11, 13}

def Fin15AnchoredAtom4019 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 9, 10, 11, 14}

def Fin15AnchoredAtom4020 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 9, 10, 12, 13}

def Fin15AnchoredAtom4021 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 9, 10, 12, 14}

def Fin15AnchoredAtom4022 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 9, 10, 13, 14}

def Fin15AnchoredAtom4023 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 9, 11, 12, 13}

def Fin15AnchoredAtom4024 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 9, 11, 12, 14}

def Fin15AnchoredAtom4025 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 9, 11, 13, 14}

def Fin15AnchoredAtom4026 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 9, 12, 13, 14}

def Fin15AnchoredAtom4027 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 10, 11, 12, 13}

def Fin15AnchoredAtom4028 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 10, 11, 12, 14}

def Fin15AnchoredAtom4029 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 10, 11, 13, 14}

def Fin15AnchoredAtom4030 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 10, 12, 13, 14}

def Fin15AnchoredAtom4031 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {2, 11, 12, 13, 14}

def Fin15AnchoredAtom4032 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 7}

def Fin15AnchoredAtom4033 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 8}

def Fin15AnchoredAtom4034 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 9}

def Fin15AnchoredAtom4035 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 10}

def Fin15AnchoredAtom4036 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 11}

def Fin15AnchoredAtom4037 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 12}

def Fin15AnchoredAtom4038 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 13}

def Fin15AnchoredAtom4039 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 14}

def Fin15AnchoredAtom4040 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 8}

def Fin15AnchoredAtom4041 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 9}

def Fin15AnchoredAtom4042 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 10}

def Fin15AnchoredAtom4043 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 11}

def Fin15AnchoredAtom4044 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 12}

def Fin15AnchoredAtom4045 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 13}

def Fin15AnchoredAtom4046 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 14}

def Fin15AnchoredAtom4047 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 9}

def Fin15AnchoredAtom4048 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 10}

def Fin15AnchoredAtom4050 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 12}

def Fin15AnchoredAtom4051 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 13}

def Fin15AnchoredAtom4052 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 14}

def Fin15AnchoredAtom4053 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 10}

def Fin15AnchoredAtom4054 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 11}

def Fin15AnchoredAtom4055 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 12}

def Fin15AnchoredAtom4056 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 13}

def Fin15AnchoredAtom4057 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 14}

def Fin15AnchoredAtom4058 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 10, 11}

def Fin15AnchoredAtom4059 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 10, 12}

def Fin15AnchoredAtom4060 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 10, 13}

def Fin15AnchoredAtom4061 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 10, 14}

def Fin15AnchoredAtom4062 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 11, 12}

def Fin15AnchoredAtom4063 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 11, 13}

def Fin15AnchoredAtom4064 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 11, 14}

def Fin15AnchoredAtom4065 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 12, 13}

def Fin15AnchoredAtom4066 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 12, 14}

def Fin15AnchoredAtom4067 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 13, 14}

def Fin15AnchoredAtom4068 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 8}

def Fin15AnchoredAtom4069 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 9}

def Fin15AnchoredAtom4070 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 10}

def Fin15AnchoredAtom4071 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 11}

def Fin15AnchoredAtom4072 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 12}

def Fin15AnchoredAtom4073 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 13}

def Fin15AnchoredAtom4074 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 14}

def Fin15AnchoredAtom4075 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 9}

def Fin15AnchoredAtom4076 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 10}

def Fin15AnchoredAtom4078 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 12}

def Fin15AnchoredAtom4079 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 13}

def Fin15AnchoredAtom4080 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 14}

def Fin15AnchoredAtom4081 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 10}

def Fin15AnchoredAtom4082 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 11}

def Fin15AnchoredAtom4083 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 12}

def Fin15AnchoredAtom4084 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 13}

def Fin15AnchoredAtom4085 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 14}

def Fin15AnchoredAtom4086 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 10, 11}

def Fin15AnchoredAtom4087 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 10, 12}

def Fin15AnchoredAtom4088 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 10, 13}

def Fin15AnchoredAtom4089 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 10, 14}

def Fin15AnchoredAtom4090 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 11, 12}

def Fin15AnchoredAtom4091 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 11, 13}

def Fin15AnchoredAtom4092 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 11, 14}

def Fin15AnchoredAtom4093 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 12, 13}

def Fin15AnchoredAtom4094 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 12, 14}

def Fin15AnchoredAtom4095 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 13, 14}

def Fin15AnchoredAtom4096 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 9}

def Fin15AnchoredAtom4097 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 10}

def Fin15AnchoredAtom4099 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 12}

def Fin15AnchoredAtom4100 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 13}

def Fin15AnchoredAtom4101 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 14}

def Fin15AnchoredAtom4102 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 10}

def Fin15AnchoredAtom4103 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 11}

def Fin15AnchoredAtom4104 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 12}

def Fin15AnchoredAtom4105 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 13}

def Fin15AnchoredAtom4106 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 14}

def Fin15AnchoredAtom4107 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 10, 11}

def Fin15AnchoredAtom4108 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 10, 12}

def Fin15AnchoredAtom4109 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 10, 13}

def Fin15AnchoredAtom4110 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 10, 14}

def Fin15AnchoredAtom4111 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 11, 12}

def Fin15AnchoredAtom4114 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 12, 13}

def Fin15AnchoredAtom4115 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 12, 14}

def Fin15AnchoredAtom4116 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 13, 14}

def Fin15AnchoredAtom4117 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 10}

def Fin15AnchoredAtom4119 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 12}

def Fin15AnchoredAtom4120 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 13}

def Fin15AnchoredAtom4121 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 14}

def Fin15AnchoredAtom4123 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 10, 12}

def Fin15AnchoredAtom4124 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 10, 13}

def Fin15AnchoredAtom4125 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 10, 14}

def Fin15AnchoredAtom4129 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 12, 13}

def Fin15AnchoredAtom4130 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 12, 14}

def Fin15AnchoredAtom4131 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 13, 14}

def Fin15AnchoredAtom4132 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 10, 11}

def Fin15AnchoredAtom4133 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 10, 12}

def Fin15AnchoredAtom4134 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 10, 13}

def Fin15AnchoredAtom4135 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 10, 14}

def Fin15AnchoredAtom4136 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 11, 12}

def Fin15AnchoredAtom4137 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 11, 13}

def Fin15AnchoredAtom4138 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 11, 14}

def Fin15AnchoredAtom4139 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 12, 13}

def Fin15AnchoredAtom4140 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 12, 14}

def Fin15AnchoredAtom4141 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 13, 14}

def Fin15AnchoredAtom4142 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 10, 11, 12}

def Fin15AnchoredAtom4143 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 10, 11, 13}

def Fin15AnchoredAtom4145 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 10, 12, 13}

def Fin15AnchoredAtom4146 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 10, 12, 14}

def Fin15AnchoredAtom4147 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 10, 13, 14}

def Fin15AnchoredAtom4148 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 11, 12, 13}

def Fin15AnchoredAtom4149 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 11, 12, 14}

def Fin15AnchoredAtom4151 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 4, 12, 13, 14}

def Fin15AnchoredAtom4152 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 8}

def Fin15AnchoredAtom4153 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 9}

def Fin15AnchoredAtom4154 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 10}

def Fin15AnchoredAtom4155 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 11}

def Fin15AnchoredAtom4156 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 12}

def Fin15AnchoredAtom4157 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 13}

def Fin15AnchoredAtom4158 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 14}

def Fin15AnchoredAtom4159 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 9}

def Fin15AnchoredAtom4160 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 10}

def Fin15AnchoredAtom4162 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 12}

def Fin15AnchoredAtom4163 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 13}

def Fin15AnchoredAtom4164 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 14}

def Fin15AnchoredAtom4165 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 10}

def Fin15AnchoredAtom4166 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 11}

def Fin15AnchoredAtom4167 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 12}

def Fin15AnchoredAtom4168 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 13}

def Fin15AnchoredAtom4169 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 14}

def Fin15AnchoredAtom4170 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 10, 11}

def Fin15AnchoredAtom4171 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 10, 12}

def Fin15AnchoredAtom4172 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 10, 13}

def Fin15AnchoredAtom4173 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 10, 14}

def Fin15AnchoredAtom4174 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 11, 12}

def Fin15AnchoredAtom4176 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 11, 14}

def Fin15AnchoredAtom4177 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 12, 13}

def Fin15AnchoredAtom4178 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 12, 14}

def Fin15AnchoredAtom4179 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 13, 14}

def Fin15AnchoredAtom4180 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 9}

def Fin15AnchoredAtom4181 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 10}

def Fin15AnchoredAtom4183 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 12}

def Fin15AnchoredAtom4184 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 13}

def Fin15AnchoredAtom4185 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 14}

def Fin15AnchoredAtom4186 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 10}

def Fin15AnchoredAtom4187 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 11}

def Fin15AnchoredAtom4188 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 12}

def Fin15AnchoredAtom4189 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 13}

def Fin15AnchoredAtom4190 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 14}

def Fin15AnchoredAtom4191 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 10, 11}

def Fin15AnchoredAtom4192 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 10, 12}

def Fin15AnchoredAtom4193 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 10, 13}

def Fin15AnchoredAtom4194 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 10, 14}

def Fin15AnchoredAtom4195 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 11, 12}

def Fin15AnchoredAtom4196 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 11, 13}

def Fin15AnchoredAtom4197 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 11, 14}

def Fin15AnchoredAtom4198 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 12, 13}

def Fin15AnchoredAtom4199 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 12, 14}

def Fin15AnchoredAtom4200 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 13, 14}

def Fin15AnchoredAtom4201 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 10}

def Fin15AnchoredAtom4203 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 12}

def Fin15AnchoredAtom4204 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 13}

def Fin15AnchoredAtom4205 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 14}

def Fin15AnchoredAtom4207 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 10, 12}

def Fin15AnchoredAtom4208 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 10, 13}

def Fin15AnchoredAtom4209 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 10, 14}

def Fin15AnchoredAtom4213 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 12, 13}

def Fin15AnchoredAtom4214 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 12, 14}

def Fin15AnchoredAtom4215 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 13, 14}

def Fin15AnchoredAtom4216 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 10, 11}

def Fin15AnchoredAtom4217 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 10, 12}

def Fin15AnchoredAtom4218 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 10, 13}

def Fin15AnchoredAtom4219 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 10, 14}

def Fin15AnchoredAtom4220 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 11, 12}

def Fin15AnchoredAtom4221 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 11, 13}

def Fin15AnchoredAtom4222 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 11, 14}

def Fin15AnchoredAtom4223 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 12, 13}

def Fin15AnchoredAtom4224 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 12, 14}

def Fin15AnchoredAtom4225 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 13, 14}

def Fin15AnchoredAtom4226 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 10, 11, 12}

def Fin15AnchoredAtom4227 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 10, 11, 13}

def Fin15AnchoredAtom4229 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 10, 12, 13}

def Fin15AnchoredAtom4230 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 10, 12, 14}

def Fin15AnchoredAtom4231 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 10, 13, 14}

def Fin15AnchoredAtom4232 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 11, 12, 13}

def Fin15AnchoredAtom4233 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 11, 12, 14}

def Fin15AnchoredAtom4234 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 11, 13, 14}

def Fin15AnchoredAtom4235 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 5, 12, 13, 14}

def Fin15AnchoredAtom4236 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 9}

def Fin15AnchoredAtom4237 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 10}

def Fin15AnchoredAtom4239 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 12}

def Fin15AnchoredAtom4240 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 13}

def Fin15AnchoredAtom4241 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 14}

def Fin15AnchoredAtom4242 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 10}

def Fin15AnchoredAtom4243 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 11}

def Fin15AnchoredAtom4244 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 12}

def Fin15AnchoredAtom4245 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 13}

def Fin15AnchoredAtom4246 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 14}

def Fin15AnchoredAtom4247 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 10, 11}

def Fin15AnchoredAtom4248 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 10, 12}

def Fin15AnchoredAtom4249 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 10, 13}

def Fin15AnchoredAtom4250 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 10, 14}

def Fin15AnchoredAtom4254 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 12, 13}

def Fin15AnchoredAtom4255 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 12, 14}

def Fin15AnchoredAtom4256 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 13, 14}

def Fin15AnchoredAtom4257 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 10}

def Fin15AnchoredAtom4259 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 12}

def Fin15AnchoredAtom4260 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 13}

def Fin15AnchoredAtom4261 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 14}

def Fin15AnchoredAtom4263 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 10, 12}

def Fin15AnchoredAtom4264 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 10, 13}

def Fin15AnchoredAtom4265 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 10, 14}

def Fin15AnchoredAtom4269 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 12, 13}

def Fin15AnchoredAtom4270 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 12, 14}

def Fin15AnchoredAtom4271 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 13, 14}

def Fin15AnchoredAtom4272 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 10, 11}

def Fin15AnchoredAtom4273 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 10, 12}

def Fin15AnchoredAtom4274 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 10, 13}

def Fin15AnchoredAtom4275 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 10, 14}

def Fin15AnchoredAtom4276 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 11, 12}

def Fin15AnchoredAtom4277 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 11, 13}

def Fin15AnchoredAtom4278 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 11, 14}

def Fin15AnchoredAtom4279 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 12, 13}

def Fin15AnchoredAtom4280 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 12, 14}

def Fin15AnchoredAtom4281 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 13, 14}

def Fin15AnchoredAtom4282 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 10, 11, 12}

def Fin15AnchoredAtom4285 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 10, 12, 13}

def Fin15AnchoredAtom4286 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 10, 12, 14}

def Fin15AnchoredAtom4287 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 10, 13, 14}

def Fin15AnchoredAtom4288 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 11, 12, 13}

def Fin15AnchoredAtom4291 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 6, 12, 13, 14}

def Fin15AnchoredAtom4292 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 9, 10}

def Fin15AnchoredAtom4294 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 9, 12}

def Fin15AnchoredAtom4295 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 9, 13}

def Fin15AnchoredAtom4296 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 9, 14}

def Fin15AnchoredAtom4298 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 10, 12}

def Fin15AnchoredAtom4299 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 10, 13}

def Fin15AnchoredAtom4300 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 10, 14}

def Fin15AnchoredAtom4304 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 12, 13}

def Fin15AnchoredAtom4305 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 12, 14}

def Fin15AnchoredAtom4306 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 13, 14}

def Fin15AnchoredAtom4307 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 10, 11}

def Fin15AnchoredAtom4308 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 10, 12}

def Fin15AnchoredAtom4309 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 10, 13}

def Fin15AnchoredAtom4310 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 10, 14}

def Fin15AnchoredAtom4311 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 11, 12}

def Fin15AnchoredAtom4312 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 11, 13}

def Fin15AnchoredAtom4313 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 11, 14}

def Fin15AnchoredAtom4314 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 12, 13}

def Fin15AnchoredAtom4315 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 12, 14}

def Fin15AnchoredAtom4316 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 13, 14}

def Fin15AnchoredAtom4317 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 10, 11, 12}

def Fin15AnchoredAtom4318 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 10, 11, 13}

def Fin15AnchoredAtom4319 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 10, 11, 14}

def Fin15AnchoredAtom4320 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 10, 12, 13}

def Fin15AnchoredAtom4321 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 10, 12, 14}

def Fin15AnchoredAtom4322 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 10, 13, 14}

def Fin15AnchoredAtom4323 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 11, 12, 13}

def Fin15AnchoredAtom4324 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 11, 12, 14}

def Fin15AnchoredAtom4326 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 7, 12, 13, 14}

def Fin15AnchoredAtom4328 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 8, 9, 10, 12}

def Fin15AnchoredAtom4329 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 8, 9, 10, 13}

def Fin15AnchoredAtom4330 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 8, 9, 10, 14}

def Fin15AnchoredAtom4334 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 8, 9, 12, 13}

def Fin15AnchoredAtom4335 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 8, 9, 12, 14}

def Fin15AnchoredAtom4336 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 8, 9, 13, 14}

def Fin15AnchoredAtom4340 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 8, 10, 12, 13}

def Fin15AnchoredAtom4341 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 8, 10, 12, 14}

def Fin15AnchoredAtom4342 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 8, 10, 13, 14}

def Fin15AnchoredAtom4346 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 8, 12, 13, 14}

def Fin15AnchoredAtom4347 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 9, 10, 11, 12}

def Fin15AnchoredAtom4348 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 9, 10, 11, 13}

def Fin15AnchoredAtom4350 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 9, 10, 12, 13}

def Fin15AnchoredAtom4351 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 9, 10, 12, 14}

def Fin15AnchoredAtom4352 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 9, 10, 13, 14}

def Fin15AnchoredAtom4353 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 9, 11, 12, 13}

def Fin15AnchoredAtom4354 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 9, 11, 12, 14}

def Fin15AnchoredAtom4356 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 9, 12, 13, 14}

def Fin15AnchoredAtom4357 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 10, 11, 12, 13}

def Fin15AnchoredAtom4358 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 10, 11, 12, 14}

def Fin15AnchoredAtom4360 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {3, 10, 12, 13, 14}

def Fin15AnchoredAtom4362 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 8}

def Fin15AnchoredAtom4363 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 9}

def Fin15AnchoredAtom4364 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 10}

def Fin15AnchoredAtom4365 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 11}

def Fin15AnchoredAtom4366 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 12}

def Fin15AnchoredAtom4367 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 13}

def Fin15AnchoredAtom4368 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 14}

def Fin15AnchoredAtom4369 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 9}

def Fin15AnchoredAtom4370 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 10}

def Fin15AnchoredAtom4372 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 12}

def Fin15AnchoredAtom4373 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 13}

def Fin15AnchoredAtom4374 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 14}

def Fin15AnchoredAtom4375 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 10}

def Fin15AnchoredAtom4376 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 11}

def Fin15AnchoredAtom4377 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 12}

def Fin15AnchoredAtom4378 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 13}

def Fin15AnchoredAtom4379 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 14}

def Fin15AnchoredAtom4380 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 10, 11}

def Fin15AnchoredAtom4381 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 10, 12}

def Fin15AnchoredAtom4382 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 10, 13}

def Fin15AnchoredAtom4383 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 10, 14}

def Fin15AnchoredAtom4384 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 11, 12}

def Fin15AnchoredAtom4385 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 11, 13}

def Fin15AnchoredAtom4386 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 11, 14}

def Fin15AnchoredAtom4387 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 12, 13}

def Fin15AnchoredAtom4388 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 12, 14}

def Fin15AnchoredAtom4389 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 13, 14}

def Fin15AnchoredAtom4390 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 9}

def Fin15AnchoredAtom4391 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 10}

def Fin15AnchoredAtom4393 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 12}

def Fin15AnchoredAtom4394 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 13}

def Fin15AnchoredAtom4395 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 14}

def Fin15AnchoredAtom4396 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 10}

def Fin15AnchoredAtom4397 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 11}

def Fin15AnchoredAtom4398 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 12}

def Fin15AnchoredAtom4399 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 13}

def Fin15AnchoredAtom4400 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 14}

def Fin15AnchoredAtom4401 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 10, 11}

def Fin15AnchoredAtom4402 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 10, 12}

def Fin15AnchoredAtom4403 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 10, 13}

def Fin15AnchoredAtom4404 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 10, 14}

def Fin15AnchoredAtom4405 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 11, 12}

def Fin15AnchoredAtom4406 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 11, 13}

def Fin15AnchoredAtom4407 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 11, 14}

def Fin15AnchoredAtom4408 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 12, 13}

def Fin15AnchoredAtom4409 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 12, 14}

def Fin15AnchoredAtom4410 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 13, 14}

def Fin15AnchoredAtom4411 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 10}

def Fin15AnchoredAtom4413 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 12}

def Fin15AnchoredAtom4414 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 13}

def Fin15AnchoredAtom4415 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 14}

def Fin15AnchoredAtom4417 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 10, 12}

def Fin15AnchoredAtom4418 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 10, 13}

def Fin15AnchoredAtom4419 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 10, 14}

def Fin15AnchoredAtom4423 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 12, 13}

def Fin15AnchoredAtom4424 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 12, 14}

def Fin15AnchoredAtom4425 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 13, 14}

def Fin15AnchoredAtom4426 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 10, 11}

def Fin15AnchoredAtom4427 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 10, 12}

def Fin15AnchoredAtom4428 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 10, 13}

def Fin15AnchoredAtom4429 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 10, 14}

def Fin15AnchoredAtom4430 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 11, 12}

def Fin15AnchoredAtom4431 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 11, 13}

def Fin15AnchoredAtom4432 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 11, 14}

def Fin15AnchoredAtom4433 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 12, 13}

def Fin15AnchoredAtom4434 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 12, 14}

def Fin15AnchoredAtom4435 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 13, 14}

def Fin15AnchoredAtom4436 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 10, 11, 12}

def Fin15AnchoredAtom4437 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 10, 11, 13}

def Fin15AnchoredAtom4438 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 10, 11, 14}

def Fin15AnchoredAtom4439 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 10, 12, 13}

def Fin15AnchoredAtom4440 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 10, 12, 14}

def Fin15AnchoredAtom4441 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 10, 13, 14}

def Fin15AnchoredAtom4442 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 11, 12, 13}

def Fin15AnchoredAtom4443 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 11, 12, 14}

def Fin15AnchoredAtom4445 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 5, 12, 13, 14}

def Fin15AnchoredAtom4446 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 9}

def Fin15AnchoredAtom4447 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 10}

def Fin15AnchoredAtom4449 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 12}

def Fin15AnchoredAtom4450 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 13}

def Fin15AnchoredAtom4451 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 14}

def Fin15AnchoredAtom4452 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 10}

def Fin15AnchoredAtom4453 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 11}

def Fin15AnchoredAtom4454 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 12}

def Fin15AnchoredAtom4455 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 13}

def Fin15AnchoredAtom4456 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 14}

def Fin15AnchoredAtom4457 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 10, 11}

def Fin15AnchoredAtom4458 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 10, 12}

def Fin15AnchoredAtom4459 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 10, 13}

def Fin15AnchoredAtom4460 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 10, 14}

def Fin15AnchoredAtom4461 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 11, 12}

def Fin15AnchoredAtom4462 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 11, 13}

def Fin15AnchoredAtom4463 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 11, 14}

def Fin15AnchoredAtom4464 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 12, 13}

def Fin15AnchoredAtom4465 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 12, 14}

def Fin15AnchoredAtom4466 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 13, 14}

def Fin15AnchoredAtom4467 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 10}

def Fin15AnchoredAtom4469 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 12}

def Fin15AnchoredAtom4470 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 13}

def Fin15AnchoredAtom4471 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 14}

def Fin15AnchoredAtom4473 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 10, 12}

def Fin15AnchoredAtom4474 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 10, 13}

def Fin15AnchoredAtom4475 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 10, 14}

def Fin15AnchoredAtom4479 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 12, 13}

def Fin15AnchoredAtom4480 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 12, 14}

def Fin15AnchoredAtom4481 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 13, 14}

def Fin15AnchoredAtom4482 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 10, 11}

def Fin15AnchoredAtom4483 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 10, 12}

def Fin15AnchoredAtom4484 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 10, 13}

def Fin15AnchoredAtom4485 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 10, 14}

def Fin15AnchoredAtom4486 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 11, 12}

def Fin15AnchoredAtom4487 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 11, 13}

def Fin15AnchoredAtom4488 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 11, 14}

def Fin15AnchoredAtom4489 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 12, 13}

def Fin15AnchoredAtom4490 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 12, 14}

def Fin15AnchoredAtom4491 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 13, 14}

def Fin15AnchoredAtom4492 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 10, 11, 12}

def Fin15AnchoredAtom4493 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 10, 11, 13}

def Fin15AnchoredAtom4494 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 10, 11, 14}

def Fin15AnchoredAtom4495 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 10, 12, 13}

def Fin15AnchoredAtom4496 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 10, 12, 14}

def Fin15AnchoredAtom4497 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 10, 13, 14}

def Fin15AnchoredAtom4498 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 11, 12, 13}

def Fin15AnchoredAtom4499 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 11, 12, 14}

def Fin15AnchoredAtom4501 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 6, 12, 13, 14}

def Fin15AnchoredAtom4502 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 10}

def Fin15AnchoredAtom4504 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 12}

def Fin15AnchoredAtom4505 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 13}

def Fin15AnchoredAtom4506 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 14}

def Fin15AnchoredAtom4508 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 10, 12}

def Fin15AnchoredAtom4509 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 10, 13}

def Fin15AnchoredAtom4510 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 10, 14}

def Fin15AnchoredAtom4514 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 12, 13}

def Fin15AnchoredAtom4515 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 12, 14}

def Fin15AnchoredAtom4516 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 13, 14}

def Fin15AnchoredAtom4517 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 10, 11}

def Fin15AnchoredAtom4518 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 10, 12}

def Fin15AnchoredAtom4519 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 10, 13}

def Fin15AnchoredAtom4520 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 10, 14}

def Fin15AnchoredAtom4521 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 11, 12}

def Fin15AnchoredAtom4522 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 11, 13}

def Fin15AnchoredAtom4523 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 11, 14}

def Fin15AnchoredAtom4524 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 12, 13}

def Fin15AnchoredAtom4525 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 12, 14}

def Fin15AnchoredAtom4526 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 13, 14}

def Fin15AnchoredAtom4527 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 10, 11, 12}

def Fin15AnchoredAtom4528 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 10, 11, 13}

def Fin15AnchoredAtom4529 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 10, 11, 14}

def Fin15AnchoredAtom4530 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 10, 12, 13}

def Fin15AnchoredAtom4531 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 10, 12, 14}

def Fin15AnchoredAtom4532 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 10, 13, 14}

def Fin15AnchoredAtom4533 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 11, 12, 13}

def Fin15AnchoredAtom4534 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 11, 12, 14}

def Fin15AnchoredAtom4536 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 7, 12, 13, 14}

def Fin15AnchoredAtom4538 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 8, 9, 10, 12}

def Fin15AnchoredAtom4539 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 8, 9, 10, 13}

def Fin15AnchoredAtom4540 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 8, 9, 10, 14}

def Fin15AnchoredAtom4544 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 8, 9, 12, 13}

def Fin15AnchoredAtom4545 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 8, 9, 12, 14}

def Fin15AnchoredAtom4546 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 8, 9, 13, 14}

def Fin15AnchoredAtom4550 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 8, 10, 12, 13}

def Fin15AnchoredAtom4551 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 8, 10, 12, 14}

def Fin15AnchoredAtom4552 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 8, 10, 13, 14}

def Fin15AnchoredAtom4556 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 8, 12, 13, 14}

def Fin15AnchoredAtom4557 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 9, 10, 11, 12}

def Fin15AnchoredAtom4558 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 9, 10, 11, 13}

def Fin15AnchoredAtom4559 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 9, 10, 11, 14}

def Fin15AnchoredAtom4560 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 9, 10, 12, 13}

def Fin15AnchoredAtom4561 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 9, 10, 12, 14}

def Fin15AnchoredAtom4562 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 9, 10, 13, 14}

def Fin15AnchoredAtom4563 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 9, 11, 12, 13}

def Fin15AnchoredAtom4564 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 9, 11, 12, 14}

def Fin15AnchoredAtom4566 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 9, 12, 13, 14}

def Fin15AnchoredAtom4567 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 10, 11, 12, 13}

def Fin15AnchoredAtom4568 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 10, 11, 12, 14}

def Fin15AnchoredAtom4570 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {4, 10, 12, 13, 14}

def Fin15AnchoredAtom4572 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 9}

def Fin15AnchoredAtom4573 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 10}

def Fin15AnchoredAtom4575 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 12}

def Fin15AnchoredAtom4576 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 13}

def Fin15AnchoredAtom4577 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 14}

def Fin15AnchoredAtom4578 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 10}

def Fin15AnchoredAtom4579 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 11}

def Fin15AnchoredAtom4580 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 12}

def Fin15AnchoredAtom4581 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 13}

def Fin15AnchoredAtom4582 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 14}

def Fin15AnchoredAtom4583 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 10, 11}

def Fin15AnchoredAtom4584 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 10, 12}

def Fin15AnchoredAtom4585 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 10, 13}

def Fin15AnchoredAtom4586 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 10, 14}

def Fin15AnchoredAtom4587 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 11, 12}

def Fin15AnchoredAtom4588 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 11, 13}

def Fin15AnchoredAtom4589 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 11, 14}

def Fin15AnchoredAtom4590 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 12, 13}

def Fin15AnchoredAtom4591 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 12, 14}

def Fin15AnchoredAtom4592 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 13, 14}

def Fin15AnchoredAtom4593 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 10}

def Fin15AnchoredAtom4595 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 12}

def Fin15AnchoredAtom4596 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 13}

def Fin15AnchoredAtom4597 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 14}

def Fin15AnchoredAtom4599 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 10, 12}

def Fin15AnchoredAtom4600 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 10, 13}

def Fin15AnchoredAtom4601 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 10, 14}

def Fin15AnchoredAtom4605 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 12, 13}

def Fin15AnchoredAtom4606 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 12, 14}

def Fin15AnchoredAtom4607 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 13, 14}

def Fin15AnchoredAtom4608 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 10, 11}

def Fin15AnchoredAtom4609 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 10, 12}

def Fin15AnchoredAtom4610 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 10, 13}

def Fin15AnchoredAtom4611 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 10, 14}

def Fin15AnchoredAtom4612 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 11, 12}

def Fin15AnchoredAtom4613 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 11, 13}

def Fin15AnchoredAtom4614 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 11, 14}

def Fin15AnchoredAtom4615 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 12, 13}

def Fin15AnchoredAtom4616 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 12, 14}

def Fin15AnchoredAtom4617 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 13, 14}

def Fin15AnchoredAtom4618 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 10, 11, 12}

def Fin15AnchoredAtom4619 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 10, 11, 13}

def Fin15AnchoredAtom4620 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 10, 11, 14}

def Fin15AnchoredAtom4621 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 10, 12, 13}

def Fin15AnchoredAtom4622 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 10, 12, 14}

def Fin15AnchoredAtom4623 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 10, 13, 14}

def Fin15AnchoredAtom4624 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 11, 12, 13}

def Fin15AnchoredAtom4625 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 11, 12, 14}

def Fin15AnchoredAtom4627 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 6, 12, 13, 14}

def Fin15AnchoredAtom4628 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 10}

def Fin15AnchoredAtom4630 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 12}

def Fin15AnchoredAtom4631 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 13}

def Fin15AnchoredAtom4632 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 14}

def Fin15AnchoredAtom4634 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 10, 12}

def Fin15AnchoredAtom4635 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 10, 13}

def Fin15AnchoredAtom4636 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 10, 14}

def Fin15AnchoredAtom4640 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 12, 13}

def Fin15AnchoredAtom4641 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 12, 14}

def Fin15AnchoredAtom4642 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 13, 14}

def Fin15AnchoredAtom4643 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 10, 11}

def Fin15AnchoredAtom4644 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 10, 12}

def Fin15AnchoredAtom4645 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 10, 13}

def Fin15AnchoredAtom4646 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 10, 14}

def Fin15AnchoredAtom4647 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 11, 12}

def Fin15AnchoredAtom4648 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 11, 13}

def Fin15AnchoredAtom4649 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 11, 14}

def Fin15AnchoredAtom4650 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 12, 13}

def Fin15AnchoredAtom4651 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 12, 14}

def Fin15AnchoredAtom4652 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 13, 14}

def Fin15AnchoredAtom4653 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 10, 11, 12}

def Fin15AnchoredAtom4654 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 10, 11, 13}

def Fin15AnchoredAtom4655 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 10, 11, 14}

def Fin15AnchoredAtom4656 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 10, 12, 13}

def Fin15AnchoredAtom4657 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 10, 12, 14}

def Fin15AnchoredAtom4658 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 10, 13, 14}

def Fin15AnchoredAtom4659 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 11, 12, 13}

def Fin15AnchoredAtom4660 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 11, 12, 14}

def Fin15AnchoredAtom4661 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 11, 13, 14}

def Fin15AnchoredAtom4662 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 7, 12, 13, 14}

def Fin15AnchoredAtom4664 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 8, 9, 10, 12}

def Fin15AnchoredAtom4665 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 8, 9, 10, 13}

def Fin15AnchoredAtom4666 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 8, 9, 10, 14}

def Fin15AnchoredAtom4670 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 8, 9, 12, 13}

def Fin15AnchoredAtom4671 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 8, 9, 12, 14}

def Fin15AnchoredAtom4672 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 8, 9, 13, 14}

def Fin15AnchoredAtom4676 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 8, 10, 12, 13}

def Fin15AnchoredAtom4677 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 8, 10, 12, 14}

def Fin15AnchoredAtom4678 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 8, 10, 13, 14}

def Fin15AnchoredAtom4682 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 8, 12, 13, 14}

def Fin15AnchoredAtom4683 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 9, 10, 11, 12}

def Fin15AnchoredAtom4684 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 9, 10, 11, 13}

def Fin15AnchoredAtom4685 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 9, 10, 11, 14}

def Fin15AnchoredAtom4686 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 9, 10, 12, 13}

def Fin15AnchoredAtom4687 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 9, 10, 12, 14}

def Fin15AnchoredAtom4688 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 9, 10, 13, 14}

def Fin15AnchoredAtom4689 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 9, 11, 12, 13}

def Fin15AnchoredAtom4690 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 9, 11, 12, 14}

def Fin15AnchoredAtom4691 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 9, 11, 13, 14}

def Fin15AnchoredAtom4692 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 9, 12, 13, 14}

def Fin15AnchoredAtom4693 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 10, 11, 12, 13}

def Fin15AnchoredAtom4694 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 10, 11, 12, 14}

def Fin15AnchoredAtom4695 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 10, 11, 13, 14}

def Fin15AnchoredAtom4696 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 10, 12, 13, 14}

def Fin15AnchoredAtom4697 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {5, 11, 12, 13, 14}

def Fin15AnchoredAtom4698 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 10}

def Fin15AnchoredAtom4700 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 12}

def Fin15AnchoredAtom4701 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 13}

def Fin15AnchoredAtom4702 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 14}

def Fin15AnchoredAtom4704 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 10, 12}

def Fin15AnchoredAtom4705 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 10, 13}

def Fin15AnchoredAtom4706 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 10, 14}

def Fin15AnchoredAtom4710 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 12, 13}

def Fin15AnchoredAtom4711 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 12, 14}

def Fin15AnchoredAtom4712 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 13, 14}

def Fin15AnchoredAtom4713 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 10, 11}

def Fin15AnchoredAtom4714 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 10, 12}

def Fin15AnchoredAtom4715 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 10, 13}

def Fin15AnchoredAtom4716 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 10, 14}

def Fin15AnchoredAtom4717 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 11, 12}

def Fin15AnchoredAtom4718 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 11, 13}

def Fin15AnchoredAtom4719 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 11, 14}

def Fin15AnchoredAtom4720 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 12, 13}

def Fin15AnchoredAtom4721 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 12, 14}

def Fin15AnchoredAtom4722 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 13, 14}

def Fin15AnchoredAtom4723 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 10, 11, 12}

def Fin15AnchoredAtom4724 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 10, 11, 13}

def Fin15AnchoredAtom4725 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 10, 11, 14}

def Fin15AnchoredAtom4726 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 10, 12, 13}

def Fin15AnchoredAtom4727 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 10, 12, 14}

def Fin15AnchoredAtom4728 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 10, 13, 14}

def Fin15AnchoredAtom4729 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 11, 12, 13}

def Fin15AnchoredAtom4730 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 11, 12, 14}

def Fin15AnchoredAtom4732 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 7, 12, 13, 14}

def Fin15AnchoredAtom4734 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 8, 9, 10, 12}

def Fin15AnchoredAtom4735 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 8, 9, 10, 13}

def Fin15AnchoredAtom4736 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 8, 9, 10, 14}

def Fin15AnchoredAtom4740 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 8, 9, 12, 13}

def Fin15AnchoredAtom4741 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 8, 9, 12, 14}

def Fin15AnchoredAtom4742 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 8, 9, 13, 14}

def Fin15AnchoredAtom4746 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 8, 10, 12, 13}

def Fin15AnchoredAtom4747 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 8, 10, 12, 14}

def Fin15AnchoredAtom4748 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 8, 10, 13, 14}

def Fin15AnchoredAtom4752 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 8, 12, 13, 14}

def Fin15AnchoredAtom4753 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 9, 10, 11, 12}

def Fin15AnchoredAtom4754 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 9, 10, 11, 13}

def Fin15AnchoredAtom4755 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 9, 10, 11, 14}

def Fin15AnchoredAtom4756 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 9, 10, 12, 13}

def Fin15AnchoredAtom4757 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 9, 10, 12, 14}

def Fin15AnchoredAtom4758 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 9, 10, 13, 14}

def Fin15AnchoredAtom4759 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 9, 11, 12, 13}

def Fin15AnchoredAtom4760 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 9, 11, 12, 14}

def Fin15AnchoredAtom4762 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 9, 12, 13, 14}

def Fin15AnchoredAtom4763 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 10, 11, 12, 13}

def Fin15AnchoredAtom4764 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 10, 11, 12, 14}

def Fin15AnchoredAtom4766 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {6, 10, 12, 13, 14}

def Fin15AnchoredAtom4769 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 8, 9, 10, 12}

def Fin15AnchoredAtom4770 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 8, 9, 10, 13}

def Fin15AnchoredAtom4771 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 8, 9, 10, 14}

def Fin15AnchoredAtom4775 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 8, 9, 12, 13}

def Fin15AnchoredAtom4776 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 8, 9, 12, 14}

def Fin15AnchoredAtom4777 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 8, 9, 13, 14}

def Fin15AnchoredAtom4781 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 8, 10, 12, 13}

def Fin15AnchoredAtom4782 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 8, 10, 12, 14}

def Fin15AnchoredAtom4783 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 8, 10, 13, 14}

def Fin15AnchoredAtom4787 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 8, 12, 13, 14}

def Fin15AnchoredAtom4788 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 9, 10, 11, 12}

def Fin15AnchoredAtom4789 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 9, 10, 11, 13}

def Fin15AnchoredAtom4790 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 9, 10, 11, 14}

def Fin15AnchoredAtom4791 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 9, 10, 12, 13}

def Fin15AnchoredAtom4792 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 9, 10, 12, 14}

def Fin15AnchoredAtom4793 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 9, 10, 13, 14}

def Fin15AnchoredAtom4794 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 9, 11, 12, 13}

def Fin15AnchoredAtom4795 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 9, 11, 12, 14}

def Fin15AnchoredAtom4796 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 9, 11, 13, 14}

def Fin15AnchoredAtom4797 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 9, 12, 13, 14}

def Fin15AnchoredAtom4798 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 10, 11, 12, 13}

def Fin15AnchoredAtom4799 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 10, 11, 12, 14}

def Fin15AnchoredAtom4800 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 10, 11, 13, 14}

def Fin15AnchoredAtom4801 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 10, 12, 13, 14}

def Fin15AnchoredAtom4802 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {7, 11, 12, 13, 14}

def Fin15AnchoredAtom4806 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {8, 9, 10, 12, 13}

def Fin15AnchoredAtom4807 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {8, 9, 10, 12, 14}

def Fin15AnchoredAtom4808 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {8, 9, 10, 13, 14}

def Fin15AnchoredAtom4812 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {8, 9, 12, 13, 14}

def Fin15AnchoredAtom4816 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {8, 10, 12, 13, 14}

def Fin15AnchoredAtom4818 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {9, 10, 11, 12, 13}

def Fin15AnchoredAtom4819 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {9, 10, 11, 12, 14}

def Fin15AnchoredAtom4820 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {9, 10, 11, 13, 14}

def Fin15AnchoredAtom4821 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {9, 10, 12, 13, 14}

def Fin15AnchoredAtom4822 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {9, 11, 12, 13, 14}

def Fin15AnchoredAtom4823 (chi : TripleColoring 15) : Prop :=
  IsStrongPolygonSet chi {10, 11, 12, 13, 14}

end ErdosSzekeres

end
