module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticInterface

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

def SynchronizedFiveFanFin11SemanticStrongQuad
    (chi : TripleColoring 11) (a b c d : Fin 11)
    (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=
  chi ⟨a, b, c, hab, hbc⟩ = chi ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
    chi ⟨a, c, d, hab.trans hbc, hcd⟩ = chi ⟨b, c, d, hbc, hcd⟩

def SynchronizedFiveFanFin11SemanticAtom0001 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 1, 2, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0002 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 1, 3, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0003 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0004 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0005 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0006 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0007 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0008 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0009 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0010 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0011 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0012 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0013 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0014 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0015 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0016 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0017 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0018 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0019 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0020 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0021 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0022 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0023 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0024 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0025 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0026 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0027 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0028 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0029 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0030 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0031 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0032 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0033 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0034 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0035 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0036 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0037 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0038 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0039 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0040 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0041 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0042 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0043 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0044 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0045 (chi : TripleColoring 11) : Prop :=
  chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0046 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0047 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0048 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0049 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0050 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0051 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0052 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0053 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0054 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0055 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0056 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0057 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0058 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0059 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0060 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0061 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0062 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0063 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0064 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0065 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0066 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0067 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0068 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0069 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0070 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0071 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0072 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0073 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0074 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0075 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0076 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0077 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0078 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0079 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0080 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0081 (chi : TripleColoring 11) : Prop :=
  chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0082 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0083 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0084 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0085 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0086 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0087 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0088 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0089 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0090 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0091 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0092 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0093 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0094 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0095 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0096 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0097 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0098 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0099 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0100 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0101 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0102 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0103 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0104 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0105 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0106 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0107 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0108 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0109 (chi : TripleColoring 11) : Prop :=
  chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0110 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0111 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0112 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0113 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0114 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0115 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0116 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0117 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0118 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0119 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0120 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0121 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0122 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0123 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0124 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0125 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0126 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0127 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0128 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0129 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0130 (chi : TripleColoring 11) : Prop :=
  chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0131 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0132 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0133 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0134 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0135 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0136 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0137 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0138 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0139 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0140 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0141 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0142 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0143 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0144 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0145 (chi : TripleColoring 11) : Prop :=
  chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0146 (chi : TripleColoring 11) : Prop :=
  chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0147 (chi : TripleColoring 11) : Prop :=
  chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0148 (chi : TripleColoring 11) : Prop :=
  chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0149 (chi : TripleColoring 11) : Prop :=
  chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0150 (chi : TripleColoring 11) : Prop :=
  chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0151 (chi : TripleColoring 11) : Prop :=
  chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0152 (chi : TripleColoring 11) : Prop :=
  chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0153 (chi : TripleColoring 11) : Prop :=
  chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0154 (chi : TripleColoring 11) : Prop :=
  chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0155 (chi : TripleColoring 11) : Prop :=
  chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0156 (chi : TripleColoring 11) : Prop :=
  chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0157 (chi : TripleColoring 11) : Prop :=
  chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0158 (chi : TripleColoring 11) : Prop :=
  chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0159 (chi : TripleColoring 11) : Prop :=
  chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0160 (chi : TripleColoring 11) : Prop :=
  chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0161 (chi : TripleColoring 11) : Prop :=
  chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0162 (chi : TripleColoring 11) : Prop :=
  chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0163 (chi : TripleColoring 11) : Prop :=
  chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0164 (chi : TripleColoring 11) : Prop :=
  chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0165 (chi : TripleColoring 11) : Prop :=
  chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left

def SynchronizedFiveFanFin11SemanticAtom0166 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 3 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0167 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 4 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0168 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 5 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0169 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0170 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0171 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0172 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0173 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 2 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0174 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 4 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0175 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 5 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0176 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0177 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0178 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0179 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0180 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 3 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0181 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 4 5 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0182 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 4 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0183 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 4 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0184 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 4 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0185 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 4 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0186 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 4 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0187 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 5 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0188 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 5 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0189 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 5 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0190 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 5 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0191 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 5 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0192 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0193 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0194 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0195 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0196 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0197 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0198 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0199 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0200 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0201 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 1 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0202 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 3 4 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0203 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0204 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0205 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0206 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 3 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0207 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0208 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 3 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0209 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 4 5 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0210 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 4 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0211 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 4 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0212 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 4 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0213 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 4 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0214 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 4 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0215 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 5 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0216 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 5 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0217 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 5 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0218 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 5 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0219 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 5 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0220 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0221 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0222 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0223 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0224 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0225 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0226 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0227 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0228 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0229 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 2 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0230 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0231 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0232 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0233 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 4 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0234 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0235 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0236 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 5 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0237 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 5 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0238 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 5 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0239 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 5 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0240 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 5 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0241 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0242 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0243 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0244 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0245 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0246 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0247 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0248 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0249 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 3 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0250 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 5 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0251 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 5 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0252 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 5 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0253 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 5 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0254 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 5 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0255 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0256 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0257 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0258 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0259 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0260 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0261 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0262 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0263 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0264 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 4 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0265 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0266 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0267 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0268 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0269 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0270 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0271 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0272 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0273 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0274 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 5 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0275 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 6 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0276 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 6 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0277 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 6 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0278 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 6 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0279 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 6 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0280 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 6 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0281 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 7 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0282 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 7 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0283 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 7 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0284 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 0 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0285 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 4 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0286 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 5 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0287 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0288 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0289 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0290 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0291 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 3 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0292 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 4 5 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0293 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 4 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0294 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 4 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0295 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 4 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0296 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 4 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0297 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 4 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0298 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 5 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0299 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 5 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0300 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 5 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0301 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 5 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0302 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 5 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0303 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0304 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0305 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0306 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0307 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0308 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0309 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0310 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0311 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0312 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 2 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0313 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 4 5 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0314 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 4 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0315 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 4 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0316 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 4 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0317 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 4 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0318 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 4 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0319 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 5 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0320 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 5 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0321 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 5 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0322 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 5 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0323 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 5 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0324 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0325 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0326 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0327 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0328 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0329 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0330 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0331 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0332 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0333 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 3 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0334 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 5 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0335 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 5 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0336 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 5 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0337 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 5 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0338 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 5 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0339 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0340 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0341 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0342 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0343 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0344 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0345 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0346 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0347 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0348 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 4 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0349 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0350 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0351 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0352 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0353 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0354 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0355 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0356 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0357 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0358 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 5 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0359 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 6 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0360 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 6 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0361 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 6 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0362 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 6 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0363 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 6 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0364 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 6 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0365 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 7 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0366 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 7 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0367 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 1 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0368 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 4 5 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0369 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 4 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0370 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 4 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0371 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 4 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0372 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 4 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0373 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 4 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0374 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 5 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0375 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 5 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0376 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 5 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0377 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 5 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0378 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 5 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0379 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0380 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0381 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0382 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0383 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0384 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0385 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0386 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0387 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 3 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0388 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 5 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0389 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 5 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0390 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 5 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0391 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 5 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0392 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 5 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0393 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0394 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0395 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0396 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0397 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0398 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0399 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0400 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0401 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0402 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 4 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0403 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0404 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0405 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0406 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0407 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0408 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0409 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0410 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0411 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0412 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 5 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0413 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0414 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0415 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0416 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0417 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0418 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 6 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0419 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 7 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0420 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 7 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0421 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 7 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0422 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 2 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0423 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 5 6 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0424 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 5 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0425 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 5 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0426 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 5 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0427 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 5 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0428 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0429 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0430 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0431 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0432 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0433 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0434 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0435 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0436 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0437 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 4 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0438 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0439 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0440 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0441 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0442 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0443 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0444 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0445 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0446 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0447 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 5 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0448 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 6 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0449 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 6 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0450 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 6 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0451 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 6 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0452 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 6 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0453 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 6 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0454 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 7 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0455 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 7 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0456 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 3 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0457 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 6 7 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0458 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 6 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0459 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 6 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0460 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 6 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0461 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0462 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0463 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0464 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0465 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0466 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 5 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0467 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 6 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0468 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 6 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0469 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 6 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0470 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 6 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0471 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 6 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0472 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 6 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0473 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 7 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0474 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 7 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0475 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 7 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0476 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 4 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0477 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 5 6 7 8 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0478 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 5 6 7 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0479 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 5 6 7 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0480 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 5 6 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0481 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 5 6 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0482 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 5 6 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0483 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 5 7 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0484 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 5 7 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0485 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 5 7 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0486 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 5 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0487 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 6 7 8 9 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0488 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 6 7 8 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0489 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 6 7 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0490 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 6 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0491 (chi : TripleColoring 11) : Prop :=
  SynchronizedFiveFanFin11SemanticStrongQuad chi 7 8 9 10 (by decide) (by decide) (by decide)

def SynchronizedFiveFanFin11SemanticAtom0492 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 4}

def SynchronizedFiveFanFin11SemanticAtom0493 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 5}

def SynchronizedFiveFanFin11SemanticAtom0494 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 6}

def SynchronizedFiveFanFin11SemanticAtom0495 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 7}

def SynchronizedFiveFanFin11SemanticAtom0496 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 8}

def SynchronizedFiveFanFin11SemanticAtom0497 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 9}

def SynchronizedFiveFanFin11SemanticAtom0498 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 10}

def SynchronizedFiveFanFin11SemanticAtom0499 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom0500 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom0501 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 7}

def SynchronizedFiveFanFin11SemanticAtom0502 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom0503 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom0504 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom0505 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0506 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0507 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0508 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0509 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0510 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0511 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0512 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0513 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0514 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0515 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0516 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0517 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0518 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0519 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0520 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom0521 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom0522 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 7}

def SynchronizedFiveFanFin11SemanticAtom0523 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom0524 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom0525 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom0526 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0527 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0528 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0529 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0530 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0531 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0532 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0533 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0534 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0535 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0536 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0537 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0538 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0539 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0540 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0541 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0542 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0543 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0544 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0545 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0546 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0547 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0548 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0549 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0550 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0551 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0552 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0553 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0554 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0555 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0556 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0557 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0558 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0559 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0560 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0561 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0562 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0563 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0564 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0565 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0566 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0567 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0568 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0569 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0570 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0571 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0572 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0573 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0574 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0575 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom0576 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom0577 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 7}

def SynchronizedFiveFanFin11SemanticAtom0578 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom0579 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom0580 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom0581 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0582 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0583 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0584 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0585 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0586 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0587 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0588 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0589 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0590 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0591 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0592 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0593 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0594 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0595 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0596 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0597 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0598 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0599 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0600 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0601 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0602 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0603 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0604 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0605 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0606 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0607 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0608 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0609 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0610 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0611 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0612 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0613 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0614 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0615 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0616 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0617 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0618 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0619 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0620 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0621 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0622 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0623 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0624 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0625 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0626 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0627 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0628 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0629 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0630 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0631 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0632 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0633 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0634 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0635 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0636 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0637 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0638 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0639 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0640 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0641 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0642 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0643 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0644 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0645 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0646 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0647 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0648 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0649 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0650 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0651 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0652 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0653 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0654 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0655 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0656 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0657 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0658 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0659 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0660 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0661 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0662 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0663 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0664 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0665 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0666 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0667 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0668 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0669 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0670 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0671 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0672 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0673 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0674 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0675 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0676 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0677 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0678 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0679 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0680 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0681 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0682 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0683 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0684 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0685 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0686 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0687 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0688 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0689 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0690 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0691 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0692 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0693 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0694 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0695 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0696 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0697 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0698 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom0699 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom0700 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 7}

def SynchronizedFiveFanFin11SemanticAtom0701 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom0702 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom0703 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom0704 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0705 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0706 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0707 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0708 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0709 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0710 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0711 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0712 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0713 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0714 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0715 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0716 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0717 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0718 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0719 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0720 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0721 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0722 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0723 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0724 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0725 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0726 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0727 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0728 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0729 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0730 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0731 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0732 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0733 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0734 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0735 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0736 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0737 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0738 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0739 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0740 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0741 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0742 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0743 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0744 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0745 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0746 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0747 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0748 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0749 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0750 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0751 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0752 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0753 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0754 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0755 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0756 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0757 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0758 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0759 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0760 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0761 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0762 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0763 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0764 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0765 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0766 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0767 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0768 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0769 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0770 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0771 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0772 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0773 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0774 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0775 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0776 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0777 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0778 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0779 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0780 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0781 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0782 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0783 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0784 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0785 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0786 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0787 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0788 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0789 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0790 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0791 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0792 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0793 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0794 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0795 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0796 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0797 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0798 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0799 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0800 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0801 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0802 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0803 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0804 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0805 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0806 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0807 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0808 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0809 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0810 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0811 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0812 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0813 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0814 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0815 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0816 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0817 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0818 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0819 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0820 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0821 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0822 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0823 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0824 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0825 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0826 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0827 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0828 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0829 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0830 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0831 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0832 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0833 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0834 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0835 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0836 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0837 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0838 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0839 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0840 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0841 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0842 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0843 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0844 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0845 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0846 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0847 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0848 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0849 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0850 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0851 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0852 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0853 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0854 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0855 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0856 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0857 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0858 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0859 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0860 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0861 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0862 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0863 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0864 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0865 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0866 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0867 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0868 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0869 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0870 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0871 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0872 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0873 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0874 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0875 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0876 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0877 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0878 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0879 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0880 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0881 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0882 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0883 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0884 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0885 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0886 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0887 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0888 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0889 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0890 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0891 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0892 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0893 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0894 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0895 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0896 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0897 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0898 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0899 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0900 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0901 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0902 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0903 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0904 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0905 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0906 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0907 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0908 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0909 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0910 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0911 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0912 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0913 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0914 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0915 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0916 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0917 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0918 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0919 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0920 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0921 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0922 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0923 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0924 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0925 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0926 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0927 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0928 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0929 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0930 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0931 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0932 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0933 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0934 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0935 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0936 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0937 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0938 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0939 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0940 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0941 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0942 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0943 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0944 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0945 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0946 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0947 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 4} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 4}

def SynchronizedFiveFanFin11SemanticAtom0948 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 5} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 5}

def SynchronizedFiveFanFin11SemanticAtom0949 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 6} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 6}

def SynchronizedFiveFanFin11SemanticAtom0950 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 7} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 7}

def SynchronizedFiveFanFin11SemanticAtom0951 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 8} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 8}

def SynchronizedFiveFanFin11SemanticAtom0952 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 9}

def SynchronizedFiveFanFin11SemanticAtom0953 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 3, 10}

def SynchronizedFiveFanFin11SemanticAtom0954 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 5} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom0955 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 6} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom0956 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 7} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 7}

def SynchronizedFiveFanFin11SemanticAtom0957 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 8} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom0958 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom0959 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom0960 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 6} ∧
    ¬IsCupSet chi {0, 1, 2, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0961 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 7} ∧
    ¬IsCupSet chi {0, 1, 2, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0962 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 8} ∧
    ¬IsCupSet chi {0, 1, 2, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0963 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0964 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0965 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 7} ∧
    ¬IsCupSet chi {0, 1, 2, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0966 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 8} ∧
    ¬IsCupSet chi {0, 1, 2, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0967 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0968 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0969 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 8} ∧
    ¬IsCupSet chi {0, 1, 2, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0970 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0971 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0972 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 9} ∧
    ¬IsCupSet chi {0, 1, 2, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0973 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0974 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 2, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0975 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 5} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom0976 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 6} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom0977 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 7} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 7}

def SynchronizedFiveFanFin11SemanticAtom0978 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 8} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom0979 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 9} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom0980 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom0981 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 6} ∧
    ¬IsCupSet chi {0, 1, 3, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0982 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 7} ∧
    ¬IsCupSet chi {0, 1, 3, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0983 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 8} ∧
    ¬IsCupSet chi {0, 1, 3, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0984 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 9} ∧
    ¬IsCupSet chi {0, 1, 3, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom0985 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom0986 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 7} ∧
    ¬IsCupSet chi {0, 1, 3, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom0987 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 8} ∧
    ¬IsCupSet chi {0, 1, 3, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom0988 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 9} ∧
    ¬IsCupSet chi {0, 1, 3, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom0989 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom0990 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 8} ∧
    ¬IsCupSet chi {0, 1, 3, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom0991 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 9} ∧
    ¬IsCupSet chi {0, 1, 3, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom0992 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom0993 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 9} ∧
    ¬IsCupSet chi {0, 1, 3, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom0994 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom0995 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 3, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom0996 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 6} ∧
    ¬IsCupSet chi {0, 1, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom0997 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 7} ∧
    ¬IsCupSet chi {0, 1, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom0998 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 8} ∧
    ¬IsCupSet chi {0, 1, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom0999 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 9} ∧
    ¬IsCupSet chi {0, 1, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1000 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 10} ∧
    ¬IsCupSet chi {0, 1, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1001 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 7} ∧
    ¬IsCupSet chi {0, 1, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1002 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 8} ∧
    ¬IsCupSet chi {0, 1, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1003 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 9} ∧
    ¬IsCupSet chi {0, 1, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1004 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 10} ∧
    ¬IsCupSet chi {0, 1, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1005 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 8} ∧
    ¬IsCupSet chi {0, 1, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1006 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 9} ∧
    ¬IsCupSet chi {0, 1, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1007 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 9} ∧
    ¬IsCupSet chi {0, 1, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1008 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 10} ∧
    ¬IsCupSet chi {0, 1, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1009 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1010 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 7} ∧
    ¬IsCupSet chi {0, 1, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1011 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 8} ∧
    ¬IsCupSet chi {0, 1, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1012 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 9} ∧
    ¬IsCupSet chi {0, 1, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1013 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 10} ∧
    ¬IsCupSet chi {0, 1, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1014 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 8} ∧
    ¬IsCupSet chi {0, 1, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1015 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 9} ∧
    ¬IsCupSet chi {0, 1, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1016 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 10} ∧
    ¬IsCupSet chi {0, 1, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1017 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 9} ∧
    ¬IsCupSet chi {0, 1, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1018 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 10} ∧
    ¬IsCupSet chi {0, 1, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1019 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1020 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 8} ∧
    ¬IsCupSet chi {0, 1, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1021 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 9} ∧
    ¬IsCupSet chi {0, 1, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1022 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 10} ∧
    ¬IsCupSet chi {0, 1, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1023 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 9} ∧
    ¬IsCupSet chi {0, 1, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1024 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 10} ∧
    ¬IsCupSet chi {0, 1, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1025 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1026 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 1, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1027 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 5} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom1028 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 6} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom1029 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 7} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 7}

def SynchronizedFiveFanFin11SemanticAtom1030 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 8} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom1031 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 9} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom1032 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom1033 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 6} ∧
    ¬IsCupSet chi {0, 2, 3, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1034 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 7} ∧
    ¬IsCupSet chi {0, 2, 3, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1035 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 8} ∧
    ¬IsCupSet chi {0, 2, 3, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1036 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 9} ∧
    ¬IsCupSet chi {0, 2, 3, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1037 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1038 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 7} ∧
    ¬IsCupSet chi {0, 2, 3, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1039 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 8} ∧
    ¬IsCupSet chi {0, 2, 3, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1040 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 9} ∧
    ¬IsCupSet chi {0, 2, 3, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1041 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1042 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 8} ∧
    ¬IsCupSet chi {0, 2, 3, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1043 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 9} ∧
    ¬IsCupSet chi {0, 2, 3, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1044 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1045 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 9} ∧
    ¬IsCupSet chi {0, 2, 3, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1046 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1047 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 3, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1048 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 6} ∧
    ¬IsCupSet chi {0, 2, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1049 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 7} ∧
    ¬IsCupSet chi {0, 2, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1050 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 8} ∧
    ¬IsCupSet chi {0, 2, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1051 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 9} ∧
    ¬IsCupSet chi {0, 2, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1052 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 10} ∧
    ¬IsCupSet chi {0, 2, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1053 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 7} ∧
    ¬IsCupSet chi {0, 2, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1054 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 8} ∧
    ¬IsCupSet chi {0, 2, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1055 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 9} ∧
    ¬IsCupSet chi {0, 2, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1056 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 10} ∧
    ¬IsCupSet chi {0, 2, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1057 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 8} ∧
    ¬IsCupSet chi {0, 2, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1058 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 9} ∧
    ¬IsCupSet chi {0, 2, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1059 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 10} ∧
    ¬IsCupSet chi {0, 2, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1060 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 9} ∧
    ¬IsCupSet chi {0, 2, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1061 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 10} ∧
    ¬IsCupSet chi {0, 2, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1062 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1063 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 7} ∧
    ¬IsCupSet chi {0, 2, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1064 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 8} ∧
    ¬IsCupSet chi {0, 2, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1065 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 9} ∧
    ¬IsCupSet chi {0, 2, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1066 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 10} ∧
    ¬IsCupSet chi {0, 2, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1067 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 8} ∧
    ¬IsCupSet chi {0, 2, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1068 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 9} ∧
    ¬IsCupSet chi {0, 2, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1069 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 10} ∧
    ¬IsCupSet chi {0, 2, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1070 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 9} ∧
    ¬IsCupSet chi {0, 2, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1071 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 10} ∧
    ¬IsCupSet chi {0, 2, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1072 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1073 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 8} ∧
    ¬IsCupSet chi {0, 2, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1074 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 9} ∧
    ¬IsCupSet chi {0, 2, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1075 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 10} ∧
    ¬IsCupSet chi {0, 2, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1076 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 9} ∧
    ¬IsCupSet chi {0, 2, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1077 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 10} ∧
    ¬IsCupSet chi {0, 2, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1078 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1079 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 9} ∧
    ¬IsCupSet chi {0, 2, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1080 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 10} ∧
    ¬IsCupSet chi {0, 2, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1081 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1082 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 2, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1083 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 6} ∧
    ¬IsCupSet chi {0, 3, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1084 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 7} ∧
    ¬IsCupSet chi {0, 3, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1085 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 8} ∧
    ¬IsCupSet chi {0, 3, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1086 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 9} ∧
    ¬IsCupSet chi {0, 3, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1087 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 10} ∧
    ¬IsCupSet chi {0, 3, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1088 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 7} ∧
    ¬IsCupSet chi {0, 3, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1089 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 8} ∧
    ¬IsCupSet chi {0, 3, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1090 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 9} ∧
    ¬IsCupSet chi {0, 3, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1091 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 10} ∧
    ¬IsCupSet chi {0, 3, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1092 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 8} ∧
    ¬IsCupSet chi {0, 3, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1093 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 9} ∧
    ¬IsCupSet chi {0, 3, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1094 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 10} ∧
    ¬IsCupSet chi {0, 3, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1095 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 9} ∧
    ¬IsCupSet chi {0, 3, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1096 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 10} ∧
    ¬IsCupSet chi {0, 3, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1097 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 10} ∧
    ¬IsCupSet chi {0, 3, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1098 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 7} ∧
    ¬IsCupSet chi {0, 3, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1099 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 8} ∧
    ¬IsCupSet chi {0, 3, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1100 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 9} ∧
    ¬IsCupSet chi {0, 3, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1101 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 10} ∧
    ¬IsCupSet chi {0, 3, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1102 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 8} ∧
    ¬IsCupSet chi {0, 3, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1103 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 9} ∧
    ¬IsCupSet chi {0, 3, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1104 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 10} ∧
    ¬IsCupSet chi {0, 3, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1105 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 9} ∧
    ¬IsCupSet chi {0, 3, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1106 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 10} ∧
    ¬IsCupSet chi {0, 3, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1107 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 10} ∧
    ¬IsCupSet chi {0, 3, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1108 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 9} ∧
    ¬IsCupSet chi {0, 3, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1109 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 10} ∧
    ¬IsCupSet chi {0, 3, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1110 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 9} ∧
    ¬IsCupSet chi {0, 3, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1111 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 10} ∧
    ¬IsCupSet chi {0, 3, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1112 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 10} ∧
    ¬IsCupSet chi {0, 3, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1113 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 10} ∧
    ¬IsCupSet chi {0, 3, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1114 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 10} ∧
    ¬IsCupSet chi {0, 3, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1115 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 3, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1116 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 7} ∧
    ¬IsCupSet chi {0, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1117 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 8} ∧
    ¬IsCupSet chi {0, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1118 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 9} ∧
    ¬IsCupSet chi {0, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1119 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 10} ∧
    ¬IsCupSet chi {0, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1120 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 8} ∧
    ¬IsCupSet chi {0, 4, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1121 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 9} ∧
    ¬IsCupSet chi {0, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1122 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 10} ∧
    ¬IsCupSet chi {0, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1123 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 9} ∧
    ¬IsCupSet chi {0, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1124 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 10} ∧
    ¬IsCupSet chi {0, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1125 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 10} ∧
    ¬IsCupSet chi {0, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1126 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 8} ∧
    ¬IsCupSet chi {0, 4, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1127 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 9} ∧
    ¬IsCupSet chi {0, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1128 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 10} ∧
    ¬IsCupSet chi {0, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1129 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 9} ∧
    ¬IsCupSet chi {0, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1130 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 10} ∧
    ¬IsCupSet chi {0, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1131 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 10} ∧
    ¬IsCupSet chi {0, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1132 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 9} ∧
    ¬IsCupSet chi {0, 4, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1133 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 10} ∧
    ¬IsCupSet chi {0, 4, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1134 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 10} ∧
    ¬IsCupSet chi {0, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1135 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1136 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 8} ∧
    ¬IsCupSet chi {0, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1137 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 9} ∧
    ¬IsCupSet chi {0, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1138 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 10} ∧
    ¬IsCupSet chi {0, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1139 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 9} ∧
    ¬IsCupSet chi {0, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1140 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 10} ∧
    ¬IsCupSet chi {0, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1141 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 10} ∧
    ¬IsCupSet chi {0, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1142 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 10} ∧
    ¬IsCupSet chi {0, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1143 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 10} ∧
    ¬IsCupSet chi {0, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1144 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1145 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 10} ∧
    ¬IsCupSet chi {0, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1146 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {0, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1147 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1148 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {0, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1149 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 5} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom1150 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 6} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom1151 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 7} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 7}

def SynchronizedFiveFanFin11SemanticAtom1152 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 8} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom1153 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 9} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom1154 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom1155 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 6} ∧
    ¬IsCupSet chi {1, 2, 3, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1156 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 7} ∧
    ¬IsCupSet chi {1, 2, 3, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1157 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 8} ∧
    ¬IsCupSet chi {1, 2, 3, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1158 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 9} ∧
    ¬IsCupSet chi {1, 2, 3, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1159 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1160 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 7} ∧
    ¬IsCupSet chi {1, 2, 3, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1161 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 8} ∧
    ¬IsCupSet chi {1, 2, 3, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1162 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 9} ∧
    ¬IsCupSet chi {1, 2, 3, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1163 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1164 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 9} ∧
    ¬IsCupSet chi {1, 2, 3, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1165 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1166 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 9} ∧
    ¬IsCupSet chi {1, 2, 3, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1167 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1168 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 3, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1169 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 6} ∧
    ¬IsCupSet chi {1, 2, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1170 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 7} ∧
    ¬IsCupSet chi {1, 2, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1171 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 8} ∧
    ¬IsCupSet chi {1, 2, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1172 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 9} ∧
    ¬IsCupSet chi {1, 2, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1173 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 10} ∧
    ¬IsCupSet chi {1, 2, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1174 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 7} ∧
    ¬IsCupSet chi {1, 2, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1175 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 8} ∧
    ¬IsCupSet chi {1, 2, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1176 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 9} ∧
    ¬IsCupSet chi {1, 2, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1177 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 10} ∧
    ¬IsCupSet chi {1, 2, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1178 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 8} ∧
    ¬IsCupSet chi {1, 2, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1179 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 9} ∧
    ¬IsCupSet chi {1, 2, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1180 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 10} ∧
    ¬IsCupSet chi {1, 2, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1181 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 9} ∧
    ¬IsCupSet chi {1, 2, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1182 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 10} ∧
    ¬IsCupSet chi {1, 2, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1183 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1184 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 7} ∧
    ¬IsCupSet chi {1, 2, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1185 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 8} ∧
    ¬IsCupSet chi {1, 2, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1186 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 9} ∧
    ¬IsCupSet chi {1, 2, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1187 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 10} ∧
    ¬IsCupSet chi {1, 2, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1188 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 8} ∧
    ¬IsCupSet chi {1, 2, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1189 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 9} ∧
    ¬IsCupSet chi {1, 2, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1190 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 10} ∧
    ¬IsCupSet chi {1, 2, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1191 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 9} ∧
    ¬IsCupSet chi {1, 2, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1192 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 10} ∧
    ¬IsCupSet chi {1, 2, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1193 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1194 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 8} ∧
    ¬IsCupSet chi {1, 2, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1195 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 9} ∧
    ¬IsCupSet chi {1, 2, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1196 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 10} ∧
    ¬IsCupSet chi {1, 2, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1197 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 9} ∧
    ¬IsCupSet chi {1, 2, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1198 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 10} ∧
    ¬IsCupSet chi {1, 2, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1199 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1200 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1201 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 8, 9, 10} ∧
    ¬IsCupSet chi {1, 2, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1202 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 6} ∧
    ¬IsCupSet chi {1, 3, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1203 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 7} ∧
    ¬IsCupSet chi {1, 3, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1204 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 8} ∧
    ¬IsCupSet chi {1, 3, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1205 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 9} ∧
    ¬IsCupSet chi {1, 3, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1206 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 10} ∧
    ¬IsCupSet chi {1, 3, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1207 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 7} ∧
    ¬IsCupSet chi {1, 3, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1208 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 8} ∧
    ¬IsCupSet chi {1, 3, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1209 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 9} ∧
    ¬IsCupSet chi {1, 3, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1210 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 10} ∧
    ¬IsCupSet chi {1, 3, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1211 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 8} ∧
    ¬IsCupSet chi {1, 3, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1212 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 9} ∧
    ¬IsCupSet chi {1, 3, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1213 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 10} ∧
    ¬IsCupSet chi {1, 3, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1214 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 9} ∧
    ¬IsCupSet chi {1, 3, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1215 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 10} ∧
    ¬IsCupSet chi {1, 3, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1216 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 9, 10} ∧
    ¬IsCupSet chi {1, 3, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1217 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 7} ∧
    ¬IsCupSet chi {1, 3, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1218 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 8} ∧
    ¬IsCupSet chi {1, 3, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1219 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 9} ∧
    ¬IsCupSet chi {1, 3, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1220 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 10} ∧
    ¬IsCupSet chi {1, 3, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1221 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 8} ∧
    ¬IsCupSet chi {1, 3, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1222 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 9} ∧
    ¬IsCupSet chi {1, 3, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1223 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 10} ∧
    ¬IsCupSet chi {1, 3, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1224 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 9} ∧
    ¬IsCupSet chi {1, 3, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1225 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 10} ∧
    ¬IsCupSet chi {1, 3, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1226 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 9, 10} ∧
    ¬IsCupSet chi {1, 3, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1227 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 9} ∧
    ¬IsCupSet chi {1, 3, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1228 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 10} ∧
    ¬IsCupSet chi {1, 3, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1229 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 9} ∧
    ¬IsCupSet chi {1, 3, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1230 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 10} ∧
    ¬IsCupSet chi {1, 3, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1231 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 9, 10} ∧
    ¬IsCupSet chi {1, 3, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1232 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 9} ∧
    ¬IsCupSet chi {1, 3, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1233 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 10} ∧
    ¬IsCupSet chi {1, 3, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1234 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 9, 10} ∧
    ¬IsCupSet chi {1, 3, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1235 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 9, 10} ∧
    ¬IsCupSet chi {1, 3, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1236 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 7} ∧
    ¬IsCupSet chi {1, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1237 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 8} ∧
    ¬IsCupSet chi {1, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1238 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 9} ∧
    ¬IsCupSet chi {1, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1239 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 10} ∧
    ¬IsCupSet chi {1, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1240 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 8} ∧
    ¬IsCupSet chi {1, 4, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1241 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 9} ∧
    ¬IsCupSet chi {1, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1242 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 10} ∧
    ¬IsCupSet chi {1, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1243 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 9} ∧
    ¬IsCupSet chi {1, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1244 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 10} ∧
    ¬IsCupSet chi {1, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1245 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 9, 10} ∧
    ¬IsCupSet chi {1, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1246 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 8} ∧
    ¬IsCupSet chi {1, 4, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1247 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 9} ∧
    ¬IsCupSet chi {1, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1248 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 10} ∧
    ¬IsCupSet chi {1, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1249 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 9} ∧
    ¬IsCupSet chi {1, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1250 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 10} ∧
    ¬IsCupSet chi {1, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1251 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 9, 10} ∧
    ¬IsCupSet chi {1, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1252 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 10} ∧
    ¬IsCupSet chi {1, 4, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1253 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 9, 10} ∧
    ¬IsCupSet chi {1, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1254 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 9, 10} ∧
    ¬IsCupSet chi {1, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1255 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 8} ∧
    ¬IsCupSet chi {1, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1256 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 9} ∧
    ¬IsCupSet chi {1, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1257 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 10} ∧
    ¬IsCupSet chi {1, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1258 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 9} ∧
    ¬IsCupSet chi {1, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1259 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 10} ∧
    ¬IsCupSet chi {1, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1260 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 9, 10} ∧
    ¬IsCupSet chi {1, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1261 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 9} ∧
    ¬IsCupSet chi {1, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1262 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 10} ∧
    ¬IsCupSet chi {1, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1263 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 9, 10} ∧
    ¬IsCupSet chi {1, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1264 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 9, 10} ∧
    ¬IsCupSet chi {1, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1265 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {1, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1266 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {1, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1267 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 6} ∧
    ¬IsCupSet chi {2, 3, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1268 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 7} ∧
    ¬IsCupSet chi {2, 3, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1269 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 8} ∧
    ¬IsCupSet chi {2, 3, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1270 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 9} ∧
    ¬IsCupSet chi {2, 3, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1271 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 10} ∧
    ¬IsCupSet chi {2, 3, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1272 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 7} ∧
    ¬IsCupSet chi {2, 3, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1273 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 8} ∧
    ¬IsCupSet chi {2, 3, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1274 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 9} ∧
    ¬IsCupSet chi {2, 3, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1275 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 10} ∧
    ¬IsCupSet chi {2, 3, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1276 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 8} ∧
    ¬IsCupSet chi {2, 3, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1277 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 9} ∧
    ¬IsCupSet chi {2, 3, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1278 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 10} ∧
    ¬IsCupSet chi {2, 3, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1279 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 9} ∧
    ¬IsCupSet chi {2, 3, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1280 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 10} ∧
    ¬IsCupSet chi {2, 3, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1281 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 10} ∧
    ¬IsCupSet chi {2, 3, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1282 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 8} ∧
    ¬IsCupSet chi {2, 3, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1283 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 9} ∧
    ¬IsCupSet chi {2, 3, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1284 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 10} ∧
    ¬IsCupSet chi {2, 3, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1285 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 8} ∧
    ¬IsCupSet chi {2, 3, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1286 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 9} ∧
    ¬IsCupSet chi {2, 3, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1287 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 10} ∧
    ¬IsCupSet chi {2, 3, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1288 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 9} ∧
    ¬IsCupSet chi {2, 3, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1289 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 10} ∧
    ¬IsCupSet chi {2, 3, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1290 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 10} ∧
    ¬IsCupSet chi {2, 3, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1291 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 9} ∧
    ¬IsCupSet chi {2, 3, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1292 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 10} ∧
    ¬IsCupSet chi {2, 3, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1293 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 9} ∧
    ¬IsCupSet chi {2, 3, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1294 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 10} ∧
    ¬IsCupSet chi {2, 3, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1295 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 10} ∧
    ¬IsCupSet chi {2, 3, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1296 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 9} ∧
    ¬IsCupSet chi {2, 3, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1297 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 10} ∧
    ¬IsCupSet chi {2, 3, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1298 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 9, 10} ∧
    ¬IsCupSet chi {2, 3, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1299 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 7} ∧
    ¬IsCupSet chi {2, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1300 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 8} ∧
    ¬IsCupSet chi {2, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1301 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 9} ∧
    ¬IsCupSet chi {2, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1302 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 10} ∧
    ¬IsCupSet chi {2, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1303 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 8} ∧
    ¬IsCupSet chi {2, 4, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1304 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 9} ∧
    ¬IsCupSet chi {2, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1305 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 10} ∧
    ¬IsCupSet chi {2, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1306 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 9} ∧
    ¬IsCupSet chi {2, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1307 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 10} ∧
    ¬IsCupSet chi {2, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1308 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 10} ∧
    ¬IsCupSet chi {2, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1309 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 8} ∧
    ¬IsCupSet chi {2, 4, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1310 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 9} ∧
    ¬IsCupSet chi {2, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1311 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 10} ∧
    ¬IsCupSet chi {2, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1312 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 9} ∧
    ¬IsCupSet chi {2, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1313 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 10} ∧
    ¬IsCupSet chi {2, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1314 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 10} ∧
    ¬IsCupSet chi {2, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1315 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 9} ∧
    ¬IsCupSet chi {2, 4, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1316 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 10} ∧
    ¬IsCupSet chi {2, 4, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1317 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 10} ∧
    ¬IsCupSet chi {2, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1318 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 9, 10} ∧
    ¬IsCupSet chi {2, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1319 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 8} ∧
    ¬IsCupSet chi {2, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1320 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 9} ∧
    ¬IsCupSet chi {2, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1321 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 10} ∧
    ¬IsCupSet chi {2, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1322 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 9} ∧
    ¬IsCupSet chi {2, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1323 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 10} ∧
    ¬IsCupSet chi {2, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1324 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 10} ∧
    ¬IsCupSet chi {2, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1325 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 9} ∧
    ¬IsCupSet chi {2, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1326 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 10} ∧
    ¬IsCupSet chi {2, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1327 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 10} ∧
    ¬IsCupSet chi {2, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1328 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 9, 10} ∧
    ¬IsCupSet chi {2, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1329 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 9} ∧
    ¬IsCupSet chi {2, 6, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1330 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 10} ∧
    ¬IsCupSet chi {2, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1331 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {2, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1332 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {2, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1333 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {2, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1334 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 7} ∧
    ¬IsCupSet chi {3, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1335 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 8} ∧
    ¬IsCupSet chi {3, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1336 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 9} ∧
    ¬IsCupSet chi {3, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1337 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 10} ∧
    ¬IsCupSet chi {3, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1338 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 8} ∧
    ¬IsCupSet chi {3, 4, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1339 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 9} ∧
    ¬IsCupSet chi {3, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1340 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 10} ∧
    ¬IsCupSet chi {3, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1341 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 9} ∧
    ¬IsCupSet chi {3, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1342 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 10} ∧
    ¬IsCupSet chi {3, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1343 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 10} ∧
    ¬IsCupSet chi {3, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1344 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 8} ∧
    ¬IsCupSet chi {3, 4, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1345 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 9} ∧
    ¬IsCupSet chi {3, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1346 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 10} ∧
    ¬IsCupSet chi {3, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1347 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 9} ∧
    ¬IsCupSet chi {3, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1348 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 10} ∧
    ¬IsCupSet chi {3, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1349 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 10} ∧
    ¬IsCupSet chi {3, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1350 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 9} ∧
    ¬IsCupSet chi {3, 4, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1351 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 10} ∧
    ¬IsCupSet chi {3, 4, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1352 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 10} ∧
    ¬IsCupSet chi {3, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1353 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 10} ∧
    ¬IsCupSet chi {3, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1354 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 10} ∧
    ¬IsCupSet chi {3, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1355 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 9} ∧
    ¬IsCupSet chi {3, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1356 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 10} ∧
    ¬IsCupSet chi {3, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1357 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 10} ∧
    ¬IsCupSet chi {3, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1358 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 9} ∧
    ¬IsCupSet chi {3, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1359 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 10} ∧
    ¬IsCupSet chi {3, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1360 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 10} ∧
    ¬IsCupSet chi {3, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1361 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 10} ∧
    ¬IsCupSet chi {3, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1362 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 10} ∧
    ¬IsCupSet chi {3, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1363 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {3, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1364 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {3, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1365 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {3, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1366 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 8} ∧
    ¬IsCupSet chi {4, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1367 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 9} ∧
    ¬IsCupSet chi {4, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1368 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 10} ∧
    ¬IsCupSet chi {4, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1369 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 9} ∧
    ¬IsCupSet chi {4, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1370 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 10} ∧
    ¬IsCupSet chi {4, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1371 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 10} ∧
    ¬IsCupSet chi {4, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1372 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 9} ∧
    ¬IsCupSet chi {4, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1373 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 10} ∧
    ¬IsCupSet chi {4, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1374 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 10} ∧
    ¬IsCupSet chi {4, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1375 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 10} ∧
    ¬IsCupSet chi {4, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1376 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 9} ∧
    ¬IsCupSet chi {4, 6, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1377 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 10} ∧
    ¬IsCupSet chi {4, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1378 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {4, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1379 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {4, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1380 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {4, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1381 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 10} ∧
    ¬IsCupSet chi {5, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1382 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 10} ∧
    ¬IsCupSet chi {5, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1383 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {5, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1384 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 10} ∧
    ¬IsCupSet chi {6, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1385 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 4} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 4}

def SynchronizedFiveFanFin11SemanticAtom1386 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 5} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 5}

def SynchronizedFiveFanFin11SemanticAtom1387 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 6} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 6}

def SynchronizedFiveFanFin11SemanticAtom1388 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 7} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 7}

def SynchronizedFiveFanFin11SemanticAtom1389 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 8} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 8}

def SynchronizedFiveFanFin11SemanticAtom1390 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 9}

def SynchronizedFiveFanFin11SemanticAtom1391 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 3, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 3, 10}

def SynchronizedFiveFanFin11SemanticAtom1392 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 5} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom1393 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 6} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom1394 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 7} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 7}

def SynchronizedFiveFanFin11SemanticAtom1395 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 8} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom1396 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom1397 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 4, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom1398 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 6} ∧
    ¬IsCapSet chi {0, 1, 2, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1399 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 7} ∧
    ¬IsCapSet chi {0, 1, 2, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1400 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 8} ∧
    ¬IsCapSet chi {0, 1, 2, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1401 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1402 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 5, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1403 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 7} ∧
    ¬IsCapSet chi {0, 1, 2, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1404 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 8} ∧
    ¬IsCapSet chi {0, 1, 2, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1405 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1406 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 6, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1407 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 8} ∧
    ¬IsCapSet chi {0, 1, 2, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1408 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1409 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 7, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1410 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 9} ∧
    ¬IsCapSet chi {0, 1, 2, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1411 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1412 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 2, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 2, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1413 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 5} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom1414 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 6} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom1415 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 7} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 7}

def SynchronizedFiveFanFin11SemanticAtom1416 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 8} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom1417 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 9} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom1418 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 4, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom1419 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 6} ∧
    ¬IsCapSet chi {0, 1, 3, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1420 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 7} ∧
    ¬IsCapSet chi {0, 1, 3, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1421 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 8} ∧
    ¬IsCapSet chi {0, 1, 3, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1422 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 9} ∧
    ¬IsCapSet chi {0, 1, 3, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1423 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 5, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1424 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 7} ∧
    ¬IsCapSet chi {0, 1, 3, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1425 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 8} ∧
    ¬IsCapSet chi {0, 1, 3, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1426 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 9} ∧
    ¬IsCapSet chi {0, 1, 3, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1427 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 6, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1428 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 8} ∧
    ¬IsCapSet chi {0, 1, 3, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1429 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 9} ∧
    ¬IsCapSet chi {0, 1, 3, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1430 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 7, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1431 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 9} ∧
    ¬IsCapSet chi {0, 1, 3, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1432 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1433 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 3, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 3, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1434 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 6} ∧
    ¬IsCapSet chi {0, 1, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1435 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 7} ∧
    ¬IsCapSet chi {0, 1, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1436 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 8} ∧
    ¬IsCapSet chi {0, 1, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1437 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 9} ∧
    ¬IsCapSet chi {0, 1, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1438 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 5, 10} ∧
    ¬IsCapSet chi {0, 1, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1439 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 7} ∧
    ¬IsCapSet chi {0, 1, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1440 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 8} ∧
    ¬IsCapSet chi {0, 1, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1441 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 9} ∧
    ¬IsCapSet chi {0, 1, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1442 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 6, 10} ∧
    ¬IsCapSet chi {0, 1, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1443 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 8} ∧
    ¬IsCapSet chi {0, 1, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1444 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 9} ∧
    ¬IsCapSet chi {0, 1, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1445 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 7, 10} ∧
    ¬IsCapSet chi {0, 1, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1446 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 9} ∧
    ¬IsCapSet chi {0, 1, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1447 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1448 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 4, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1449 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 7} ∧
    ¬IsCapSet chi {0, 1, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1450 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 8} ∧
    ¬IsCapSet chi {0, 1, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1451 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 9} ∧
    ¬IsCapSet chi {0, 1, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1452 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 6, 10} ∧
    ¬IsCapSet chi {0, 1, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1453 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 8} ∧
    ¬IsCapSet chi {0, 1, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1454 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 9} ∧
    ¬IsCapSet chi {0, 1, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1455 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 7, 10} ∧
    ¬IsCapSet chi {0, 1, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1456 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 9} ∧
    ¬IsCapSet chi {0, 1, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1457 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1458 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 5, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1459 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 8} ∧
    ¬IsCapSet chi {0, 1, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1460 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 9} ∧
    ¬IsCapSet chi {0, 1, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1461 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 7, 10} ∧
    ¬IsCapSet chi {0, 1, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1462 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 9} ∧
    ¬IsCapSet chi {0, 1, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1463 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1464 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 6, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1465 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 1, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1466 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1467 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 1, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 1, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1468 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 5} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom1469 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 6} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom1470 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 7} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 7}

def SynchronizedFiveFanFin11SemanticAtom1471 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 8} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom1472 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 9} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom1473 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom1474 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 6} ∧
    ¬IsCapSet chi {0, 2, 3, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1475 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 7} ∧
    ¬IsCapSet chi {0, 2, 3, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1476 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 8} ∧
    ¬IsCapSet chi {0, 2, 3, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1477 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 9} ∧
    ¬IsCapSet chi {0, 2, 3, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1478 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1479 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 7} ∧
    ¬IsCapSet chi {0, 2, 3, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1480 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 8} ∧
    ¬IsCapSet chi {0, 2, 3, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1481 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 9} ∧
    ¬IsCapSet chi {0, 2, 3, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1482 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1483 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 8} ∧
    ¬IsCapSet chi {0, 2, 3, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1484 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 9} ∧
    ¬IsCapSet chi {0, 2, 3, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1485 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1486 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 9} ∧
    ¬IsCapSet chi {0, 2, 3, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1487 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1488 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 3, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1489 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 6} ∧
    ¬IsCapSet chi {0, 2, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1490 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 7} ∧
    ¬IsCapSet chi {0, 2, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1491 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 8} ∧
    ¬IsCapSet chi {0, 2, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1492 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 9} ∧
    ¬IsCapSet chi {0, 2, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1493 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 10} ∧
    ¬IsCapSet chi {0, 2, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1494 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 7} ∧
    ¬IsCapSet chi {0, 2, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1495 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 8} ∧
    ¬IsCapSet chi {0, 2, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1496 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 9} ∧
    ¬IsCapSet chi {0, 2, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1497 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 10} ∧
    ¬IsCapSet chi {0, 2, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1498 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 8} ∧
    ¬IsCapSet chi {0, 2, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1499 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 9} ∧
    ¬IsCapSet chi {0, 2, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1500 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 10} ∧
    ¬IsCapSet chi {0, 2, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1501 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 9} ∧
    ¬IsCapSet chi {0, 2, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1502 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 10} ∧
    ¬IsCapSet chi {0, 2, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1503 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1504 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 7} ∧
    ¬IsCapSet chi {0, 2, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1505 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 8} ∧
    ¬IsCapSet chi {0, 2, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1506 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 9} ∧
    ¬IsCapSet chi {0, 2, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1507 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 10} ∧
    ¬IsCapSet chi {0, 2, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1508 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 8} ∧
    ¬IsCapSet chi {0, 2, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1509 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 9} ∧
    ¬IsCapSet chi {0, 2, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1510 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 10} ∧
    ¬IsCapSet chi {0, 2, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1511 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 9} ∧
    ¬IsCapSet chi {0, 2, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1512 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 10} ∧
    ¬IsCapSet chi {0, 2, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1513 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1514 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 8} ∧
    ¬IsCapSet chi {0, 2, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1515 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 9} ∧
    ¬IsCapSet chi {0, 2, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1516 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 10} ∧
    ¬IsCapSet chi {0, 2, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1517 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 9} ∧
    ¬IsCapSet chi {0, 2, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1518 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 10} ∧
    ¬IsCapSet chi {0, 2, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1519 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1520 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 9} ∧
    ¬IsCapSet chi {0, 2, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1521 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 2, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1522 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1523 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 2, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1524 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 6} ∧
    ¬IsCapSet chi {0, 3, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1525 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 7} ∧
    ¬IsCapSet chi {0, 3, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1526 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 8} ∧
    ¬IsCapSet chi {0, 3, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1527 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 9} ∧
    ¬IsCapSet chi {0, 3, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1528 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 10} ∧
    ¬IsCapSet chi {0, 3, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1529 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 7} ∧
    ¬IsCapSet chi {0, 3, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1530 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 8} ∧
    ¬IsCapSet chi {0, 3, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1531 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 9} ∧
    ¬IsCapSet chi {0, 3, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1532 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 10} ∧
    ¬IsCapSet chi {0, 3, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1533 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 8} ∧
    ¬IsCapSet chi {0, 3, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1534 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 9} ∧
    ¬IsCapSet chi {0, 3, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1535 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 10} ∧
    ¬IsCapSet chi {0, 3, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1536 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 9} ∧
    ¬IsCapSet chi {0, 3, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1537 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 10} ∧
    ¬IsCapSet chi {0, 3, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1538 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 10} ∧
    ¬IsCapSet chi {0, 3, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1539 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 7} ∧
    ¬IsCapSet chi {0, 3, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1540 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 8} ∧
    ¬IsCapSet chi {0, 3, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1541 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 9} ∧
    ¬IsCapSet chi {0, 3, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1542 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 10} ∧
    ¬IsCapSet chi {0, 3, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1543 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 8} ∧
    ¬IsCapSet chi {0, 3, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1544 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 9} ∧
    ¬IsCapSet chi {0, 3, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1545 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 10} ∧
    ¬IsCapSet chi {0, 3, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1546 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 9} ∧
    ¬IsCapSet chi {0, 3, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1547 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 10} ∧
    ¬IsCapSet chi {0, 3, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1548 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 10} ∧
    ¬IsCapSet chi {0, 3, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1549 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 9} ∧
    ¬IsCapSet chi {0, 3, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1550 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 10} ∧
    ¬IsCapSet chi {0, 3, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1551 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 9} ∧
    ¬IsCapSet chi {0, 3, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1552 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 10} ∧
    ¬IsCapSet chi {0, 3, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1553 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 10} ∧
    ¬IsCapSet chi {0, 3, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1554 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 3, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1555 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 3, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1556 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 3, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1557 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 7} ∧
    ¬IsCapSet chi {0, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1558 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 8} ∧
    ¬IsCapSet chi {0, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1559 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 9} ∧
    ¬IsCapSet chi {0, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1560 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 10} ∧
    ¬IsCapSet chi {0, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1561 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 8} ∧
    ¬IsCapSet chi {0, 4, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1562 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 9} ∧
    ¬IsCapSet chi {0, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1563 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 10} ∧
    ¬IsCapSet chi {0, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1564 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 9} ∧
    ¬IsCapSet chi {0, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1565 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 10} ∧
    ¬IsCapSet chi {0, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1566 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 10} ∧
    ¬IsCapSet chi {0, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1567 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 8} ∧
    ¬IsCapSet chi {0, 4, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1568 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 9} ∧
    ¬IsCapSet chi {0, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1569 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 10} ∧
    ¬IsCapSet chi {0, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1570 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 9} ∧
    ¬IsCapSet chi {0, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1571 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 10} ∧
    ¬IsCapSet chi {0, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1572 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 10} ∧
    ¬IsCapSet chi {0, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1573 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 4, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1574 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1575 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1576 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 8} ∧
    ¬IsCapSet chi {0, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1577 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 9} ∧
    ¬IsCapSet chi {0, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1578 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 10} ∧
    ¬IsCapSet chi {0, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1579 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 9} ∧
    ¬IsCapSet chi {0, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1580 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 10} ∧
    ¬IsCapSet chi {0, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1581 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 10} ∧
    ¬IsCapSet chi {0, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1582 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 9} ∧
    ¬IsCapSet chi {0, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1583 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1584 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1585 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1586 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 10} ∧
    ¬IsCapSet chi {0, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1587 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {0, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1588 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {0, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1589 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 5} ∧
    ¬IsCapSet chi {1, 2, 3, 4, 5}

def SynchronizedFiveFanFin11SemanticAtom1590 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 6} ∧
    ¬IsCapSet chi {1, 2, 3, 4, 6}

def SynchronizedFiveFanFin11SemanticAtom1591 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 8} ∧
    ¬IsCapSet chi {1, 2, 3, 4, 8}

def SynchronizedFiveFanFin11SemanticAtom1592 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 9} ∧
    ¬IsCapSet chi {1, 2, 3, 4, 9}

def SynchronizedFiveFanFin11SemanticAtom1593 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 4, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 4, 10}

def SynchronizedFiveFanFin11SemanticAtom1594 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 6} ∧
    ¬IsCapSet chi {1, 2, 3, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1595 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 7} ∧
    ¬IsCapSet chi {1, 2, 3, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1596 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 8} ∧
    ¬IsCapSet chi {1, 2, 3, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1597 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 9} ∧
    ¬IsCapSet chi {1, 2, 3, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1598 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 5, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1599 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 7} ∧
    ¬IsCapSet chi {1, 2, 3, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1600 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 8} ∧
    ¬IsCapSet chi {1, 2, 3, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1601 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 9} ∧
    ¬IsCapSet chi {1, 2, 3, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1602 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 6, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1603 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 8} ∧
    ¬IsCapSet chi {1, 2, 3, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1604 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 9} ∧
    ¬IsCapSet chi {1, 2, 3, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1605 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 7, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1606 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 9} ∧
    ¬IsCapSet chi {1, 2, 3, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1607 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 8, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1608 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 3, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 3, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1609 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 6} ∧
    ¬IsCapSet chi {1, 2, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1610 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 7} ∧
    ¬IsCapSet chi {1, 2, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1611 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 8} ∧
    ¬IsCapSet chi {1, 2, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1612 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 9} ∧
    ¬IsCapSet chi {1, 2, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1613 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 5, 10} ∧
    ¬IsCapSet chi {1, 2, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1614 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 7} ∧
    ¬IsCapSet chi {1, 2, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1615 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 8} ∧
    ¬IsCapSet chi {1, 2, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1616 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 9} ∧
    ¬IsCapSet chi {1, 2, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1617 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 6, 10} ∧
    ¬IsCapSet chi {1, 2, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1618 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 8} ∧
    ¬IsCapSet chi {1, 2, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1619 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 9} ∧
    ¬IsCapSet chi {1, 2, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1620 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 7, 10} ∧
    ¬IsCapSet chi {1, 2, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1621 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 9} ∧
    ¬IsCapSet chi {1, 2, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1622 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 8, 10} ∧
    ¬IsCapSet chi {1, 2, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1623 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 4, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1624 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 7} ∧
    ¬IsCapSet chi {1, 2, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1625 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 8} ∧
    ¬IsCapSet chi {1, 2, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1626 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 9} ∧
    ¬IsCapSet chi {1, 2, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1627 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 6, 10} ∧
    ¬IsCapSet chi {1, 2, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1628 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 8} ∧
    ¬IsCapSet chi {1, 2, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1629 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 9} ∧
    ¬IsCapSet chi {1, 2, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1630 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 7, 10} ∧
    ¬IsCapSet chi {1, 2, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1631 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 9} ∧
    ¬IsCapSet chi {1, 2, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1632 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 8, 10} ∧
    ¬IsCapSet chi {1, 2, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1633 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 5, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1634 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 8} ∧
    ¬IsCapSet chi {1, 2, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1635 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 9} ∧
    ¬IsCapSet chi {1, 2, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1636 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 7, 10} ∧
    ¬IsCapSet chi {1, 2, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1637 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 9} ∧
    ¬IsCapSet chi {1, 2, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1638 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 8, 10} ∧
    ¬IsCapSet chi {1, 2, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1639 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 6, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1640 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 8, 10} ∧
    ¬IsCapSet chi {1, 2, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1641 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 7, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1642 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 2, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 2, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1643 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 6} ∧
    ¬IsCapSet chi {1, 3, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1644 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 7} ∧
    ¬IsCapSet chi {1, 3, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1645 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 8} ∧
    ¬IsCapSet chi {1, 3, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1646 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 9} ∧
    ¬IsCapSet chi {1, 3, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1647 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 5, 10} ∧
    ¬IsCapSet chi {1, 3, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1648 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 7} ∧
    ¬IsCapSet chi {1, 3, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1649 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 8} ∧
    ¬IsCapSet chi {1, 3, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1650 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 9} ∧
    ¬IsCapSet chi {1, 3, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1651 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 6, 10} ∧
    ¬IsCapSet chi {1, 3, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1652 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 9} ∧
    ¬IsCapSet chi {1, 3, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1653 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 7, 10} ∧
    ¬IsCapSet chi {1, 3, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1654 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 9} ∧
    ¬IsCapSet chi {1, 3, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1655 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 8, 10} ∧
    ¬IsCapSet chi {1, 3, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1656 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 4, 9, 10} ∧
    ¬IsCapSet chi {1, 3, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1657 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 7} ∧
    ¬IsCapSet chi {1, 3, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1658 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 8} ∧
    ¬IsCapSet chi {1, 3, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1659 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 9} ∧
    ¬IsCapSet chi {1, 3, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1660 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 6, 10} ∧
    ¬IsCapSet chi {1, 3, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1661 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 8} ∧
    ¬IsCapSet chi {1, 3, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1662 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 9} ∧
    ¬IsCapSet chi {1, 3, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1663 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 7, 10} ∧
    ¬IsCapSet chi {1, 3, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1664 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 9} ∧
    ¬IsCapSet chi {1, 3, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1665 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 8, 10} ∧
    ¬IsCapSet chi {1, 3, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1666 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 5, 9, 10} ∧
    ¬IsCapSet chi {1, 3, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1667 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 8} ∧
    ¬IsCapSet chi {1, 3, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1668 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 9} ∧
    ¬IsCapSet chi {1, 3, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1669 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 7, 10} ∧
    ¬IsCapSet chi {1, 3, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1670 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 9} ∧
    ¬IsCapSet chi {1, 3, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1671 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 8, 10} ∧
    ¬IsCapSet chi {1, 3, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1672 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 6, 9, 10} ∧
    ¬IsCapSet chi {1, 3, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1673 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 9} ∧
    ¬IsCapSet chi {1, 3, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1674 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 8, 10} ∧
    ¬IsCapSet chi {1, 3, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1675 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 7, 9, 10} ∧
    ¬IsCapSet chi {1, 3, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1676 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 3, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 3, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1677 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 7} ∧
    ¬IsCapSet chi {1, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1678 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 8} ∧
    ¬IsCapSet chi {1, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1679 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 9} ∧
    ¬IsCapSet chi {1, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1680 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 6, 10} ∧
    ¬IsCapSet chi {1, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1681 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 8} ∧
    ¬IsCapSet chi {1, 4, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1682 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 9} ∧
    ¬IsCapSet chi {1, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1683 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 7, 10} ∧
    ¬IsCapSet chi {1, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1684 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 9} ∧
    ¬IsCapSet chi {1, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1685 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 8, 10} ∧
    ¬IsCapSet chi {1, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1686 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 5, 9, 10} ∧
    ¬IsCapSet chi {1, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1687 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 8} ∧
    ¬IsCapSet chi {1, 4, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1688 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 9} ∧
    ¬IsCapSet chi {1, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1689 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 7, 10} ∧
    ¬IsCapSet chi {1, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1690 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 9} ∧
    ¬IsCapSet chi {1, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1691 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 8, 10} ∧
    ¬IsCapSet chi {1, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1692 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 6, 9, 10} ∧
    ¬IsCapSet chi {1, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1693 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 8, 10} ∧
    ¬IsCapSet chi {1, 4, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1694 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 7, 9, 10} ∧
    ¬IsCapSet chi {1, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1695 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 4, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1696 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 8} ∧
    ¬IsCapSet chi {1, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1697 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 9} ∧
    ¬IsCapSet chi {1, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1698 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 7, 10} ∧
    ¬IsCapSet chi {1, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1699 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 9} ∧
    ¬IsCapSet chi {1, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1700 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 8, 10} ∧
    ¬IsCapSet chi {1, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1701 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 6, 9, 10} ∧
    ¬IsCapSet chi {1, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1702 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 9} ∧
    ¬IsCapSet chi {1, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1703 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 8, 10} ∧
    ¬IsCapSet chi {1, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1704 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 7, 9, 10} ∧
    ¬IsCapSet chi {1, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1705 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 5, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1706 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 9} ∧
    ¬IsCapSet chi {1, 6, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1707 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 8, 10} ∧
    ¬IsCapSet chi {1, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1708 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {1, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1709 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1710 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {1, 7, 8, 9, 10} ∧
    ¬IsCapSet chi {1, 7, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1711 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 6} ∧
    ¬IsCapSet chi {2, 3, 4, 5, 6}

def SynchronizedFiveFanFin11SemanticAtom1712 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 7} ∧
    ¬IsCapSet chi {2, 3, 4, 5, 7}

def SynchronizedFiveFanFin11SemanticAtom1713 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 8} ∧
    ¬IsCapSet chi {2, 3, 4, 5, 8}

def SynchronizedFiveFanFin11SemanticAtom1714 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 9} ∧
    ¬IsCapSet chi {2, 3, 4, 5, 9}

def SynchronizedFiveFanFin11SemanticAtom1715 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 10} ∧
    ¬IsCapSet chi {2, 3, 4, 5, 10}

def SynchronizedFiveFanFin11SemanticAtom1716 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 7} ∧
    ¬IsCapSet chi {2, 3, 4, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1717 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 8} ∧
    ¬IsCapSet chi {2, 3, 4, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1718 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 9} ∧
    ¬IsCapSet chi {2, 3, 4, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1719 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 10} ∧
    ¬IsCapSet chi {2, 3, 4, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1720 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 8} ∧
    ¬IsCapSet chi {2, 3, 4, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1721 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 9} ∧
    ¬IsCapSet chi {2, 3, 4, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1722 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 10} ∧
    ¬IsCapSet chi {2, 3, 4, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1723 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 9} ∧
    ¬IsCapSet chi {2, 3, 4, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1724 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 10} ∧
    ¬IsCapSet chi {2, 3, 4, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1725 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 10} ∧
    ¬IsCapSet chi {2, 3, 4, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1726 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 7} ∧
    ¬IsCapSet chi {2, 3, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1727 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 8} ∧
    ¬IsCapSet chi {2, 3, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1728 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 9} ∧
    ¬IsCapSet chi {2, 3, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1729 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 10} ∧
    ¬IsCapSet chi {2, 3, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1730 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 8} ∧
    ¬IsCapSet chi {2, 3, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1731 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 9} ∧
    ¬IsCapSet chi {2, 3, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1732 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 10} ∧
    ¬IsCapSet chi {2, 3, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1733 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 9} ∧
    ¬IsCapSet chi {2, 3, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1734 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 10} ∧
    ¬IsCapSet chi {2, 3, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1735 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 10} ∧
    ¬IsCapSet chi {2, 3, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1736 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 9} ∧
    ¬IsCapSet chi {2, 3, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1737 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 10} ∧
    ¬IsCapSet chi {2, 3, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1738 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 9} ∧
    ¬IsCapSet chi {2, 3, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1739 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 10} ∧
    ¬IsCapSet chi {2, 3, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1740 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 10} ∧
    ¬IsCapSet chi {2, 3, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1741 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 9} ∧
    ¬IsCapSet chi {2, 3, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1742 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 10} ∧
    ¬IsCapSet chi {2, 3, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1743 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 10} ∧
    ¬IsCapSet chi {2, 3, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1744 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 9, 10} ∧
    ¬IsCapSet chi {2, 3, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1745 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 7} ∧
    ¬IsCapSet chi {2, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1746 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 8} ∧
    ¬IsCapSet chi {2, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1747 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 9} ∧
    ¬IsCapSet chi {2, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1748 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 10} ∧
    ¬IsCapSet chi {2, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1749 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 8} ∧
    ¬IsCapSet chi {2, 4, 5, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1750 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 9} ∧
    ¬IsCapSet chi {2, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1751 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 10} ∧
    ¬IsCapSet chi {2, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1752 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 9} ∧
    ¬IsCapSet chi {2, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1753 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 10} ∧
    ¬IsCapSet chi {2, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1754 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 10} ∧
    ¬IsCapSet chi {2, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1755 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 8} ∧
    ¬IsCapSet chi {2, 4, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1756 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 9} ∧
    ¬IsCapSet chi {2, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1757 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 10} ∧
    ¬IsCapSet chi {2, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1758 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 9} ∧
    ¬IsCapSet chi {2, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1759 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 10} ∧
    ¬IsCapSet chi {2, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1760 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 10} ∧
    ¬IsCapSet chi {2, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1761 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 10} ∧
    ¬IsCapSet chi {2, 4, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1762 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 10} ∧
    ¬IsCapSet chi {2, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1763 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 9, 10} ∧
    ¬IsCapSet chi {2, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1764 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 8} ∧
    ¬IsCapSet chi {2, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1765 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 9} ∧
    ¬IsCapSet chi {2, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1766 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 10} ∧
    ¬IsCapSet chi {2, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1767 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 9} ∧
    ¬IsCapSet chi {2, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1768 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 10} ∧
    ¬IsCapSet chi {2, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1769 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 10} ∧
    ¬IsCapSet chi {2, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1770 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 9} ∧
    ¬IsCapSet chi {2, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1771 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 10} ∧
    ¬IsCapSet chi {2, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1772 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 10} ∧
    ¬IsCapSet chi {2, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1773 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 9, 10} ∧
    ¬IsCapSet chi {2, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1774 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 10} ∧
    ¬IsCapSet chi {2, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1775 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {2, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1776 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {2, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1777 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 7} ∧
    ¬IsCapSet chi {3, 4, 5, 6, 7}

def SynchronizedFiveFanFin11SemanticAtom1778 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 8} ∧
    ¬IsCapSet chi {3, 4, 5, 6, 8}

def SynchronizedFiveFanFin11SemanticAtom1779 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 9} ∧
    ¬IsCapSet chi {3, 4, 5, 6, 9}

def SynchronizedFiveFanFin11SemanticAtom1780 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 10} ∧
    ¬IsCapSet chi {3, 4, 5, 6, 10}

def SynchronizedFiveFanFin11SemanticAtom1781 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 9} ∧
    ¬IsCapSet chi {3, 4, 5, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1782 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 10} ∧
    ¬IsCapSet chi {3, 4, 5, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1783 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 9} ∧
    ¬IsCapSet chi {3, 4, 5, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1784 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 10} ∧
    ¬IsCapSet chi {3, 4, 5, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1785 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 10} ∧
    ¬IsCapSet chi {3, 4, 5, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1786 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 9} ∧
    ¬IsCapSet chi {3, 4, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1787 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 10} ∧
    ¬IsCapSet chi {3, 4, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1788 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 9} ∧
    ¬IsCapSet chi {3, 4, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1789 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 10} ∧
    ¬IsCapSet chi {3, 4, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1790 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 10} ∧
    ¬IsCapSet chi {3, 4, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1791 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 10} ∧
    ¬IsCapSet chi {3, 4, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1792 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 10} ∧
    ¬IsCapSet chi {3, 4, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1793 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 8} ∧
    ¬IsCapSet chi {3, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1794 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 9} ∧
    ¬IsCapSet chi {3, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1795 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 10} ∧
    ¬IsCapSet chi {3, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1796 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 9} ∧
    ¬IsCapSet chi {3, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1797 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 10} ∧
    ¬IsCapSet chi {3, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1798 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 10} ∧
    ¬IsCapSet chi {3, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1799 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 9} ∧
    ¬IsCapSet chi {3, 5, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1800 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 10} ∧
    ¬IsCapSet chi {3, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1801 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 10} ∧
    ¬IsCapSet chi {3, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1802 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 10} ∧
    ¬IsCapSet chi {3, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1803 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 9} ∧
    ¬IsCapSet chi {3, 6, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1804 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {3, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1805 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {3, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1806 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 8} ∧
    ¬IsCapSet chi {4, 5, 6, 7, 8}

def SynchronizedFiveFanFin11SemanticAtom1807 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 9} ∧
    ¬IsCapSet chi {4, 5, 6, 7, 9}

def SynchronizedFiveFanFin11SemanticAtom1808 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 10} ∧
    ¬IsCapSet chi {4, 5, 6, 7, 10}

def SynchronizedFiveFanFin11SemanticAtom1809 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 9} ∧
    ¬IsCapSet chi {4, 5, 6, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1810 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 10} ∧
    ¬IsCapSet chi {4, 5, 6, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1811 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 10} ∧
    ¬IsCapSet chi {4, 5, 6, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1812 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 10} ∧
    ¬IsCapSet chi {4, 5, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1813 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 10} ∧
    ¬IsCapSet chi {4, 5, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1814 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 10} ∧
    ¬IsCapSet chi {4, 5, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1815 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 10} ∧
    ¬IsCapSet chi {4, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1816 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {4, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1817 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {4, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1818 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 9} ∧
    ¬IsCapSet chi {5, 6, 7, 8, 9}

def SynchronizedFiveFanFin11SemanticAtom1819 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 10} ∧
    ¬IsCapSet chi {5, 6, 7, 8, 10}

def SynchronizedFiveFanFin11SemanticAtom1820 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 10} ∧
    ¬IsCapSet chi {5, 6, 7, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1821 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 10} ∧
    ¬IsCapSet chi {5, 6, 8, 9, 10}

def SynchronizedFiveFanFin11SemanticAtom1822 (chi : TripleColoring 11) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 10} ∧
    ¬IsCapSet chi {5, 7, 8, 9, 10}

end ErdosSzekeres

end
