module

public import ErdosSzekeres.SynchronizedFiveFanFin11WindowTransport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-- The exact Fin13 support conclusion certified by the LRAT core. -/
def PredecessorHalfFin13Conclusion (chi : TripleColoring 13) : Prop :=
  ∃ support : Finset (Fin 13),
    support.card = 7 ∧
    ¬ContainsStrongPolygonSet chi support 5

/-- The two equalities contributed by one ordered quadruple to the
strong-polygon predicate. -/
def PredecessorHalfFin13StrongQuad (chi : TripleColoring 13)
    (a b c d : Fin 13) (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=
  chi ⟨a, b, c, hab, hbc⟩ = chi ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
    chi ⟨a, c, d, hab.trans hbc, hcd⟩ = chi ⟨b, c, d, hbc, hcd⟩

def PredecessorHalfFin13Atom0012 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0013 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0014 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0015 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0016 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0017 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 2, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0018 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0019 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0021 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 2, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0022 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 3, 4, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0023 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0024 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0025 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 3, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0026 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0027 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0028 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0030 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 3, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0031 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0032 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 4, 6, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0033 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0034 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 4, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0035 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0036 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0038 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 4, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0039 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0040 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0041 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0042 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0043 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0045 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 5, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0046 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0047 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0048 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0049 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0051 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 6, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0052 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0053 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0054 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 7, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0056 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 7, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0057 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0058 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 8, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0060 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 8, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0061 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0063 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 9, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0065 (chi : TripleColoring 13) : Prop :=
  chi ⟨0, 10, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0122 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0123 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0124 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0125 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0126 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0127 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0128 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0129 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0130 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0131 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0132 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0133 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0134 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0135 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0136 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0137 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0138 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0139 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0140 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0141 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0142 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0143 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0144 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0145 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0146 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0147 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0148 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0149 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0150 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0151 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0152 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0153 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0154 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0155 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0156 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0157 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0158 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0159 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0160 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0161 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0162 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0163 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0164 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0165 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0166 (chi : TripleColoring 13) : Prop :=
  chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0167 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0168 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0169 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0170 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0171 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0172 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0173 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0174 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0175 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0176 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0177 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0178 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0179 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0180 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0181 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0182 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0183 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0184 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0185 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0186 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0187 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0188 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0189 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0190 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0191 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0192 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0193 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0194 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0195 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0196 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0197 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0198 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0199 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0200 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0201 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0202 (chi : TripleColoring 13) : Prop :=
  chi ⟨3, 11, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0203 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0204 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0205 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0206 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0207 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0208 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0209 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0210 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0211 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0212 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0213 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0214 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0215 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0216 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0217 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0218 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0219 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0220 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0221 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0222 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0223 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0224 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0225 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0226 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0227 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0228 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 10, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0229 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 10, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0230 (chi : TripleColoring 13) : Prop :=
  chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0231 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0232 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0233 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0234 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0235 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0236 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0237 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0238 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0239 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0240 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0241 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0242 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0243 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0244 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0245 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0246 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0247 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0248 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0249 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 10, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0250 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 10, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0251 (chi : TripleColoring 13) : Prop :=
  chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0252 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0253 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0254 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0255 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0256 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0257 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0258 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0259 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0260 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0261 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0262 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0263 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0264 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0265 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0266 (chi : TripleColoring 13) : Prop :=
  chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0267 (chi : TripleColoring 13) : Prop :=
  chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0268 (chi : TripleColoring 13) : Prop :=
  chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0269 (chi : TripleColoring 13) : Prop :=
  chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0270 (chi : TripleColoring 13) : Prop :=
  chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0271 (chi : TripleColoring 13) : Prop :=
  chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0272 (chi : TripleColoring 13) : Prop :=
  chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0273 (chi : TripleColoring 13) : Prop :=
  chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0274 (chi : TripleColoring 13) : Prop :=
  chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0275 (chi : TripleColoring 13) : Prop :=
  chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0276 (chi : TripleColoring 13) : Prop :=
  chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0277 (chi : TripleColoring 13) : Prop :=
  chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0278 (chi : TripleColoring 13) : Prop :=
  chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0279 (chi : TripleColoring 13) : Prop :=
  chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0280 (chi : TripleColoring 13) : Prop :=
  chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0281 (chi : TripleColoring 13) : Prop :=
  chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0282 (chi : TripleColoring 13) : Prop :=
  chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0283 (chi : TripleColoring 13) : Prop :=
  chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0284 (chi : TripleColoring 13) : Prop :=
  chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0285 (chi : TripleColoring 13) : Prop :=
  chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0286 (chi : TripleColoring 13) : Prop :=
  chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left

def PredecessorHalfFin13Atom0342 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 3 4 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0343 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 3 5 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0344 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 3 6 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0345 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 3 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0346 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 3 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0347 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 3 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0348 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 3 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0350 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 3 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0351 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 4 5 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0352 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 4 6 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0353 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 4 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0354 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 4 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0355 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 4 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0356 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 4 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0358 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 4 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0359 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 5 6 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0360 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 5 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0361 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 5 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0362 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 5 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0363 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 5 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0365 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 5 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0366 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 6 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0367 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 6 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0368 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 6 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0369 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 6 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0371 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 6 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0372 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0373 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0374 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0376 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0377 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0378 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0380 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0381 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0383 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0385 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 2 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0387 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 4 5 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0388 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 4 6 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0389 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 4 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0390 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 4 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0391 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 4 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0392 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 4 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0394 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 4 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0395 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 5 6 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0396 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 5 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0397 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 5 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0398 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 5 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0399 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 5 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0401 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 5 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0402 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 6 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0403 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 6 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0404 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 6 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0405 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 6 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0407 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 6 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0408 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0409 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0410 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0412 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0413 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0414 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0416 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0417 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0419 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0421 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 3 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0423 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 5 6 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0424 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 5 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0425 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 5 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0426 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 5 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0427 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 5 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0429 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 5 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0430 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 6 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0431 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 6 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0432 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 6 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0433 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 6 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0435 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 6 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0436 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0437 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0438 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0440 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0441 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0442 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0444 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0445 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0447 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0449 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 4 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0451 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 6 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0452 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 6 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0453 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 6 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0454 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 6 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0456 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 6 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0457 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0458 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0459 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0461 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0462 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0463 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0465 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0466 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0468 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0470 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 5 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0472 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 6 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0473 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 6 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0474 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 6 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0476 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 6 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0477 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 6 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0478 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 6 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0480 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 6 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0481 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 6 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0483 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 6 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0485 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 6 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0487 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 7 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0488 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 7 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0490 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 7 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0491 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 7 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0493 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 7 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0495 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 7 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0497 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 8 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0499 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 8 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0501 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 8 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0504 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 0 9 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0672 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 4 5 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0673 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 4 6 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0674 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 4 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0675 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 4 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0676 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 4 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0677 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 4 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0678 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 4 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0679 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 4 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0680 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 5 6 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0681 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 5 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0682 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 5 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0683 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 5 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0684 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 5 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0685 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 5 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0686 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 5 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0687 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 6 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0688 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 6 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0689 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 6 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0690 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 6 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0691 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 6 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0692 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 6 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0693 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0694 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0695 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0696 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 7 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0697 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0698 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0699 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0700 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0701 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0702 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0703 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0704 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0705 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0706 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0707 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 3 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0708 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 5 6 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0709 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 5 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0710 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 5 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0711 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 5 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0712 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 5 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0713 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 5 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0714 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 5 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0715 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 6 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0716 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 6 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0717 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 6 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0718 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 6 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0719 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 6 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0720 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 6 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0721 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0722 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0723 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0724 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 7 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0725 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0726 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0727 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0728 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0729 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0730 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0731 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0732 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0733 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0734 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0735 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 4 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0736 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 6 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0737 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 6 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0738 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 6 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0739 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 6 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0740 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 6 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0741 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 6 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0742 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0743 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0744 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0745 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 7 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0746 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0747 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0748 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0749 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0750 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0751 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0752 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0753 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0754 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0755 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0756 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 5 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0757 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0758 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0759 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0760 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 7 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0761 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0762 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0763 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0764 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0765 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0766 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0767 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0768 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0769 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0770 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0771 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 6 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0772 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 7 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0773 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 7 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0774 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 7 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0775 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 7 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0776 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 7 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0777 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 7 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0778 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 7 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0779 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 7 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0780 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 7 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0781 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 7 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0782 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 8 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0783 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 8 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0784 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 8 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0785 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 8 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0786 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 8 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0787 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 8 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0788 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 9 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0789 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 9 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0790 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 9 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0791 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 2 10 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0792 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 5 6 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0793 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 5 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0794 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 5 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0795 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 5 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0796 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 5 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0797 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 5 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0798 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 5 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0799 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 6 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0800 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 6 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0801 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 6 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0802 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 6 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0803 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 6 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0804 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 6 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0805 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0806 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0807 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0808 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 7 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0809 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0810 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0811 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0812 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0813 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0814 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0815 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0816 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0817 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0818 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0819 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 4 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0820 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 6 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0821 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 6 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0822 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 6 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0823 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 6 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0824 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 6 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0825 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 6 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0826 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0827 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0828 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0829 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 7 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0830 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0831 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0832 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0833 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0834 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0835 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0836 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0837 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0838 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0839 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0840 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 5 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0841 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0842 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0843 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0844 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 7 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0845 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0846 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0847 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0848 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0849 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0850 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0851 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0852 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0853 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0854 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0855 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 6 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0856 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 7 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0857 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 7 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0858 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 7 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0859 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 7 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0860 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 7 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0861 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 7 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0862 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 7 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0863 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 7 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0864 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 7 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0865 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 7 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0866 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 8 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0867 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 8 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0868 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 8 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0869 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 8 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0870 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 8 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0871 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 8 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0872 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 9 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0873 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 9 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0874 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 9 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0875 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 3 10 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0876 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 6 7 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0877 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 6 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0878 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 6 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0879 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 6 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0880 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 6 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0881 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 6 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0882 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0883 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0884 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0885 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 7 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0886 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0887 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0888 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0889 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0890 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0891 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0892 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0893 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0894 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0895 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0896 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 5 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0897 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0898 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0899 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0900 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 7 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0901 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0902 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0903 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0904 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0905 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0906 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0907 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0908 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0909 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0910 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0911 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 6 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0912 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 7 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0913 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 7 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0914 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 7 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0915 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 7 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0916 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 7 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0917 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 7 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0918 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 7 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0919 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 7 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0920 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 7 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0921 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 7 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0922 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 8 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0923 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 8 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0924 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 8 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0925 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 8 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0926 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 8 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0927 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 8 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0928 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 9 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0929 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 9 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0930 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 9 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0931 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 4 10 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0932 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 7 8 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0933 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 7 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0934 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 7 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0935 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 7 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0936 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 7 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0937 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0938 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0939 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0940 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0941 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0942 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0943 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0944 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0945 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0946 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 6 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0947 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 7 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0948 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 7 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0949 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 7 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0950 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 7 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0951 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 7 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0952 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 7 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0953 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 7 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0954 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 7 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0955 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 7 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0956 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 7 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0957 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 8 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0958 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 8 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0959 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 8 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0960 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 8 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0961 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 8 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0962 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 8 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0963 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 9 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0964 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 9 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0965 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 9 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0966 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 5 10 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0967 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 7 8 9 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0968 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 7 8 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0969 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 7 8 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0970 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 7 8 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0971 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 7 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0972 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 7 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0973 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 7 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0974 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 7 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0975 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 7 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0976 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 7 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0977 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 8 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0978 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 8 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0979 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 8 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0980 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 8 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0981 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 8 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0982 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 8 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0983 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 9 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0984 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 9 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0985 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 9 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0986 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 6 10 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0987 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 7 8 9 10 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0988 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 7 8 9 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0989 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 7 8 9 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0990 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 7 8 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0991 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 7 8 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0992 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 7 8 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0993 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 7 9 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0994 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 7 9 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0995 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 7 9 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0996 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 7 10 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0997 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 8 9 10 11 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0998 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 8 9 10 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom0999 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 8 9 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom1000 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 8 10 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom1001 (chi : TripleColoring 13) : Prop :=
  PredecessorHalfFin13StrongQuad chi 9 10 11 12 (by decide) (by decide) (by decide)

def PredecessorHalfFin13Atom1167 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 5}

def PredecessorHalfFin13Atom1168 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 6}

def PredecessorHalfFin13Atom1169 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 7}

def PredecessorHalfFin13Atom1170 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 8}

def PredecessorHalfFin13Atom1171 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 9}

def PredecessorHalfFin13Atom1172 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 10}

def PredecessorHalfFin13Atom1174 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 4, 12}

def PredecessorHalfFin13Atom1175 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 6}

def PredecessorHalfFin13Atom1176 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 7}

def PredecessorHalfFin13Atom1177 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 8}

def PredecessorHalfFin13Atom1178 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 9}

def PredecessorHalfFin13Atom1179 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 10}

def PredecessorHalfFin13Atom1181 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 5, 12}

def PredecessorHalfFin13Atom1182 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 7}

def PredecessorHalfFin13Atom1183 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 8}

def PredecessorHalfFin13Atom1184 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 9}

def PredecessorHalfFin13Atom1185 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 10}

def PredecessorHalfFin13Atom1187 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 6, 12}

def PredecessorHalfFin13Atom1188 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 8}

def PredecessorHalfFin13Atom1189 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 9}

def PredecessorHalfFin13Atom1190 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 10}

def PredecessorHalfFin13Atom1192 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 7, 12}

def PredecessorHalfFin13Atom1193 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 9}

def PredecessorHalfFin13Atom1194 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 10}

def PredecessorHalfFin13Atom1196 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 8, 12}

def PredecessorHalfFin13Atom1197 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 10}

def PredecessorHalfFin13Atom1199 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 9, 12}

def PredecessorHalfFin13Atom1201 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 3, 10, 12}

def PredecessorHalfFin13Atom1203 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 6}

def PredecessorHalfFin13Atom1204 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 7}

def PredecessorHalfFin13Atom1205 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 8}

def PredecessorHalfFin13Atom1206 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 9}

def PredecessorHalfFin13Atom1207 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 10}

def PredecessorHalfFin13Atom1209 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 5, 12}

def PredecessorHalfFin13Atom1210 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 7}

def PredecessorHalfFin13Atom1211 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 8}

def PredecessorHalfFin13Atom1212 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 9}

def PredecessorHalfFin13Atom1213 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 10}

def PredecessorHalfFin13Atom1215 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 6, 12}

def PredecessorHalfFin13Atom1216 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 8}

def PredecessorHalfFin13Atom1217 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 9}

def PredecessorHalfFin13Atom1218 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 10}

def PredecessorHalfFin13Atom1220 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 7, 12}

def PredecessorHalfFin13Atom1221 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 9}

def PredecessorHalfFin13Atom1222 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 10}

def PredecessorHalfFin13Atom1224 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 8, 12}

def PredecessorHalfFin13Atom1225 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 10}

def PredecessorHalfFin13Atom1227 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 9, 12}

def PredecessorHalfFin13Atom1229 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 4, 10, 12}

def PredecessorHalfFin13Atom1231 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 7}

def PredecessorHalfFin13Atom1232 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 8}

def PredecessorHalfFin13Atom1233 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 9}

def PredecessorHalfFin13Atom1234 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 10}

def PredecessorHalfFin13Atom1236 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 6, 12}

def PredecessorHalfFin13Atom1237 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 8}

def PredecessorHalfFin13Atom1238 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 9}

def PredecessorHalfFin13Atom1239 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 10}

def PredecessorHalfFin13Atom1241 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 7, 12}

def PredecessorHalfFin13Atom1242 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 9}

def PredecessorHalfFin13Atom1243 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 10}

def PredecessorHalfFin13Atom1245 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 8, 12}

def PredecessorHalfFin13Atom1246 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 10}

def PredecessorHalfFin13Atom1248 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 9, 12}

def PredecessorHalfFin13Atom1250 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 5, 10, 12}

def PredecessorHalfFin13Atom1252 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 8}

def PredecessorHalfFin13Atom1253 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 9}

def PredecessorHalfFin13Atom1254 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 10}

def PredecessorHalfFin13Atom1256 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 7, 12}

def PredecessorHalfFin13Atom1257 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 9}

def PredecessorHalfFin13Atom1258 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 10}

def PredecessorHalfFin13Atom1260 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 8, 12}

def PredecessorHalfFin13Atom1261 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 10}

def PredecessorHalfFin13Atom1263 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 9, 12}

def PredecessorHalfFin13Atom1265 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 6, 10, 12}

def PredecessorHalfFin13Atom1267 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 9}

def PredecessorHalfFin13Atom1268 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 10}

def PredecessorHalfFin13Atom1270 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 8, 12}

def PredecessorHalfFin13Atom1271 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 10}

def PredecessorHalfFin13Atom1273 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 9, 12}

def PredecessorHalfFin13Atom1275 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 7, 10, 12}

def PredecessorHalfFin13Atom1277 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 9, 10}

def PredecessorHalfFin13Atom1279 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 9, 12}

def PredecessorHalfFin13Atom1281 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 8, 10, 12}

def PredecessorHalfFin13Atom1284 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 2, 9, 10, 12}

def PredecessorHalfFin13Atom1287 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 6}

def PredecessorHalfFin13Atom1288 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 7}

def PredecessorHalfFin13Atom1289 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 8}

def PredecessorHalfFin13Atom1290 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 9}

def PredecessorHalfFin13Atom1291 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 10}

def PredecessorHalfFin13Atom1293 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 5, 12}

def PredecessorHalfFin13Atom1294 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 7}

def PredecessorHalfFin13Atom1295 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 8}

def PredecessorHalfFin13Atom1296 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 9}

def PredecessorHalfFin13Atom1297 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 10}

def PredecessorHalfFin13Atom1299 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 6, 12}

def PredecessorHalfFin13Atom1300 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 8}

def PredecessorHalfFin13Atom1301 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 9}

def PredecessorHalfFin13Atom1302 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 10}

def PredecessorHalfFin13Atom1304 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 7, 12}

def PredecessorHalfFin13Atom1305 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 9}

def PredecessorHalfFin13Atom1306 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 10}

def PredecessorHalfFin13Atom1308 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 8, 12}

def PredecessorHalfFin13Atom1309 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 10}

def PredecessorHalfFin13Atom1311 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 9, 12}

def PredecessorHalfFin13Atom1313 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 4, 10, 12}

def PredecessorHalfFin13Atom1315 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 7}

def PredecessorHalfFin13Atom1316 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 8}

def PredecessorHalfFin13Atom1317 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 9}

def PredecessorHalfFin13Atom1318 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 10}

def PredecessorHalfFin13Atom1320 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 6, 12}

def PredecessorHalfFin13Atom1321 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 8}

def PredecessorHalfFin13Atom1322 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 9}

def PredecessorHalfFin13Atom1323 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 10}

def PredecessorHalfFin13Atom1325 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 7, 12}

def PredecessorHalfFin13Atom1326 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 9}

def PredecessorHalfFin13Atom1327 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 10}

def PredecessorHalfFin13Atom1329 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 8, 12}

def PredecessorHalfFin13Atom1330 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 10}

def PredecessorHalfFin13Atom1332 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 9, 12}

def PredecessorHalfFin13Atom1334 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 5, 10, 12}

def PredecessorHalfFin13Atom1336 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 8}

def PredecessorHalfFin13Atom1337 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 9}

def PredecessorHalfFin13Atom1338 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 10}

def PredecessorHalfFin13Atom1340 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 7, 12}

def PredecessorHalfFin13Atom1341 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 9}

def PredecessorHalfFin13Atom1342 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 10}

def PredecessorHalfFin13Atom1344 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 8, 12}

def PredecessorHalfFin13Atom1345 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 10}

def PredecessorHalfFin13Atom1347 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 9, 12}

def PredecessorHalfFin13Atom1349 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 6, 10, 12}

def PredecessorHalfFin13Atom1351 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 9}

def PredecessorHalfFin13Atom1352 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 10}

def PredecessorHalfFin13Atom1354 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 8, 12}

def PredecessorHalfFin13Atom1355 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 10}

def PredecessorHalfFin13Atom1357 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 9, 12}

def PredecessorHalfFin13Atom1359 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 7, 10, 12}

def PredecessorHalfFin13Atom1361 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 9, 10}

def PredecessorHalfFin13Atom1363 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 9, 12}

def PredecessorHalfFin13Atom1365 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 8, 10, 12}

def PredecessorHalfFin13Atom1368 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 3, 9, 10, 12}

def PredecessorHalfFin13Atom1371 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 7}

def PredecessorHalfFin13Atom1372 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 8}

def PredecessorHalfFin13Atom1373 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 9}

def PredecessorHalfFin13Atom1374 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 10}

def PredecessorHalfFin13Atom1376 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 6, 12}

def PredecessorHalfFin13Atom1377 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 8}

def PredecessorHalfFin13Atom1378 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 9}

def PredecessorHalfFin13Atom1379 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 10}

def PredecessorHalfFin13Atom1381 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 7, 12}

def PredecessorHalfFin13Atom1382 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 9}

def PredecessorHalfFin13Atom1383 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 10}

def PredecessorHalfFin13Atom1385 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 8, 12}

def PredecessorHalfFin13Atom1386 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 10}

def PredecessorHalfFin13Atom1388 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 9, 12}

def PredecessorHalfFin13Atom1390 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 5, 10, 12}

def PredecessorHalfFin13Atom1392 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 8}

def PredecessorHalfFin13Atom1393 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 9}

def PredecessorHalfFin13Atom1394 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 10}

def PredecessorHalfFin13Atom1396 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 7, 12}

def PredecessorHalfFin13Atom1397 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 9}

def PredecessorHalfFin13Atom1398 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 10}

def PredecessorHalfFin13Atom1400 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 8, 12}

def PredecessorHalfFin13Atom1401 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 10}

def PredecessorHalfFin13Atom1403 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 9, 12}

def PredecessorHalfFin13Atom1405 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 6, 10, 12}

def PredecessorHalfFin13Atom1407 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 9}

def PredecessorHalfFin13Atom1408 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 10}

def PredecessorHalfFin13Atom1410 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 8, 12}

def PredecessorHalfFin13Atom1411 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 10}

def PredecessorHalfFin13Atom1413 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 9, 12}

def PredecessorHalfFin13Atom1415 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 7, 10, 12}

def PredecessorHalfFin13Atom1417 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 9, 10}

def PredecessorHalfFin13Atom1419 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 9, 12}

def PredecessorHalfFin13Atom1421 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 8, 10, 12}

def PredecessorHalfFin13Atom1424 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 4, 9, 10, 12}

def PredecessorHalfFin13Atom1427 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 8}

def PredecessorHalfFin13Atom1428 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 9}

def PredecessorHalfFin13Atom1429 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 10}

def PredecessorHalfFin13Atom1431 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 7, 12}

def PredecessorHalfFin13Atom1432 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 9}

def PredecessorHalfFin13Atom1433 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 10}

def PredecessorHalfFin13Atom1435 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 8, 12}

def PredecessorHalfFin13Atom1436 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 10}

def PredecessorHalfFin13Atom1438 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 9, 12}

def PredecessorHalfFin13Atom1440 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 6, 10, 12}

def PredecessorHalfFin13Atom1442 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 9}

def PredecessorHalfFin13Atom1443 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 10}

def PredecessorHalfFin13Atom1445 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 8, 12}

def PredecessorHalfFin13Atom1446 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 10}

def PredecessorHalfFin13Atom1448 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 9, 12}

def PredecessorHalfFin13Atom1450 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 7, 10, 12}

def PredecessorHalfFin13Atom1452 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 9, 10}

def PredecessorHalfFin13Atom1454 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 9, 12}

def PredecessorHalfFin13Atom1456 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 8, 10, 12}

def PredecessorHalfFin13Atom1459 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 5, 9, 10, 12}

def PredecessorHalfFin13Atom1462 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 9}

def PredecessorHalfFin13Atom1463 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 10}

def PredecessorHalfFin13Atom1465 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 8, 12}

def PredecessorHalfFin13Atom1466 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 10}

def PredecessorHalfFin13Atom1468 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 9, 12}

def PredecessorHalfFin13Atom1470 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 6, 7, 10, 12}

def PredecessorHalfFin13Atom1472 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 9, 10}

def PredecessorHalfFin13Atom1474 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 9, 12}

def PredecessorHalfFin13Atom1476 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 6, 8, 10, 12}

def PredecessorHalfFin13Atom1479 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 6, 9, 10, 12}

def PredecessorHalfFin13Atom1482 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 9, 10}

def PredecessorHalfFin13Atom1484 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 9, 12}

def PredecessorHalfFin13Atom1486 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 7, 8, 10, 12}

def PredecessorHalfFin13Atom1489 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 7, 9, 10, 12}

def PredecessorHalfFin13Atom1493 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {0, 8, 9, 10, 12}

def PredecessorHalfFin13Atom1827 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 6}

def PredecessorHalfFin13Atom1828 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 7}

def PredecessorHalfFin13Atom1829 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 8}

def PredecessorHalfFin13Atom1830 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 9}

def PredecessorHalfFin13Atom1831 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 10}

def PredecessorHalfFin13Atom1832 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 11}

def PredecessorHalfFin13Atom1833 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 5, 12}

def PredecessorHalfFin13Atom1834 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 7}

def PredecessorHalfFin13Atom1835 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 8}

def PredecessorHalfFin13Atom1836 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 9}

def PredecessorHalfFin13Atom1837 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 10}

def PredecessorHalfFin13Atom1838 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 11}

def PredecessorHalfFin13Atom1839 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 6, 12}

def PredecessorHalfFin13Atom1840 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 8}

def PredecessorHalfFin13Atom1841 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 9}

def PredecessorHalfFin13Atom1842 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 10}

def PredecessorHalfFin13Atom1843 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 11}

def PredecessorHalfFin13Atom1844 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 7, 12}

def PredecessorHalfFin13Atom1845 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 9}

def PredecessorHalfFin13Atom1846 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 10}

def PredecessorHalfFin13Atom1847 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 11}

def PredecessorHalfFin13Atom1848 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 8, 12}

def PredecessorHalfFin13Atom1849 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 10}

def PredecessorHalfFin13Atom1850 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 11}

def PredecessorHalfFin13Atom1851 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 9, 12}

def PredecessorHalfFin13Atom1852 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 10, 11}

def PredecessorHalfFin13Atom1853 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 10, 12}

def PredecessorHalfFin13Atom1854 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 4, 11, 12}

def PredecessorHalfFin13Atom1855 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 7}

def PredecessorHalfFin13Atom1856 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 8}

def PredecessorHalfFin13Atom1857 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 9}

def PredecessorHalfFin13Atom1858 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 10}

def PredecessorHalfFin13Atom1859 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 11}

def PredecessorHalfFin13Atom1860 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 6, 12}

def PredecessorHalfFin13Atom1861 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 8}

def PredecessorHalfFin13Atom1862 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 9}

def PredecessorHalfFin13Atom1863 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 10}

def PredecessorHalfFin13Atom1864 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 11}

def PredecessorHalfFin13Atom1865 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 7, 12}

def PredecessorHalfFin13Atom1866 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 9}

def PredecessorHalfFin13Atom1867 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 10}

def PredecessorHalfFin13Atom1868 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 11}

def PredecessorHalfFin13Atom1869 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 8, 12}

def PredecessorHalfFin13Atom1870 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 10}

def PredecessorHalfFin13Atom1871 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 11}

def PredecessorHalfFin13Atom1872 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 9, 12}

def PredecessorHalfFin13Atom1873 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 10, 11}

def PredecessorHalfFin13Atom1874 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 10, 12}

def PredecessorHalfFin13Atom1875 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 5, 11, 12}

def PredecessorHalfFin13Atom1876 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 8}

def PredecessorHalfFin13Atom1877 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 9}

def PredecessorHalfFin13Atom1878 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 10}

def PredecessorHalfFin13Atom1879 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 11}

def PredecessorHalfFin13Atom1880 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 7, 12}

def PredecessorHalfFin13Atom1881 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 9}

def PredecessorHalfFin13Atom1882 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 10}

def PredecessorHalfFin13Atom1883 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 11}

def PredecessorHalfFin13Atom1884 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 8, 12}

def PredecessorHalfFin13Atom1885 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 10}

def PredecessorHalfFin13Atom1886 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 11}

def PredecessorHalfFin13Atom1887 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 9, 12}

def PredecessorHalfFin13Atom1888 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 10, 11}

def PredecessorHalfFin13Atom1889 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 10, 12}

def PredecessorHalfFin13Atom1890 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 6, 11, 12}

def PredecessorHalfFin13Atom1891 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 9}

def PredecessorHalfFin13Atom1892 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 10}

def PredecessorHalfFin13Atom1893 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 11}

def PredecessorHalfFin13Atom1894 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 8, 12}

def PredecessorHalfFin13Atom1895 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 10}

def PredecessorHalfFin13Atom1896 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 11}

def PredecessorHalfFin13Atom1897 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 9, 12}

def PredecessorHalfFin13Atom1898 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 10, 11}

def PredecessorHalfFin13Atom1899 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 10, 12}

def PredecessorHalfFin13Atom1900 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 7, 11, 12}

def PredecessorHalfFin13Atom1901 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 9, 10}

def PredecessorHalfFin13Atom1902 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 9, 11}

def PredecessorHalfFin13Atom1903 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 9, 12}

def PredecessorHalfFin13Atom1904 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 10, 11}

def PredecessorHalfFin13Atom1905 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 10, 12}

def PredecessorHalfFin13Atom1906 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 8, 11, 12}

def PredecessorHalfFin13Atom1907 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 10, 11}

def PredecessorHalfFin13Atom1908 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 10, 12}

def PredecessorHalfFin13Atom1909 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 9, 11, 12}

def PredecessorHalfFin13Atom1910 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 3, 10, 11, 12}

def PredecessorHalfFin13Atom1911 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 7}

def PredecessorHalfFin13Atom1912 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 8}

def PredecessorHalfFin13Atom1913 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 9}

def PredecessorHalfFin13Atom1914 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 10}

def PredecessorHalfFin13Atom1915 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 11}

def PredecessorHalfFin13Atom1916 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 6, 12}

def PredecessorHalfFin13Atom1917 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 8}

def PredecessorHalfFin13Atom1918 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 9}

def PredecessorHalfFin13Atom1919 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 10}

def PredecessorHalfFin13Atom1920 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 11}

def PredecessorHalfFin13Atom1921 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 7, 12}

def PredecessorHalfFin13Atom1922 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 9}

def PredecessorHalfFin13Atom1923 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 10}

def PredecessorHalfFin13Atom1924 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 11}

def PredecessorHalfFin13Atom1925 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 8, 12}

def PredecessorHalfFin13Atom1926 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 10}

def PredecessorHalfFin13Atom1927 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 11}

def PredecessorHalfFin13Atom1928 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 9, 12}

def PredecessorHalfFin13Atom1929 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 10, 11}

def PredecessorHalfFin13Atom1930 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 10, 12}

def PredecessorHalfFin13Atom1931 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 5, 11, 12}

def PredecessorHalfFin13Atom1932 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 8}

def PredecessorHalfFin13Atom1933 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 9}

def PredecessorHalfFin13Atom1934 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 10}

def PredecessorHalfFin13Atom1935 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 11}

def PredecessorHalfFin13Atom1936 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 7, 12}

def PredecessorHalfFin13Atom1937 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 9}

def PredecessorHalfFin13Atom1938 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 10}

def PredecessorHalfFin13Atom1939 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 11}

def PredecessorHalfFin13Atom1940 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 8, 12}

def PredecessorHalfFin13Atom1941 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 10}

def PredecessorHalfFin13Atom1942 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 11}

def PredecessorHalfFin13Atom1943 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 9, 12}

def PredecessorHalfFin13Atom1944 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 10, 11}

def PredecessorHalfFin13Atom1945 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 10, 12}

def PredecessorHalfFin13Atom1946 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 6, 11, 12}

def PredecessorHalfFin13Atom1947 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 9}

def PredecessorHalfFin13Atom1948 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 10}

def PredecessorHalfFin13Atom1949 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 11}

def PredecessorHalfFin13Atom1950 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 8, 12}

def PredecessorHalfFin13Atom1951 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 10}

def PredecessorHalfFin13Atom1952 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 11}

def PredecessorHalfFin13Atom1953 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 9, 12}

def PredecessorHalfFin13Atom1954 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 10, 11}

def PredecessorHalfFin13Atom1955 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 10, 12}

def PredecessorHalfFin13Atom1956 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 7, 11, 12}

def PredecessorHalfFin13Atom1957 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 9, 10}

def PredecessorHalfFin13Atom1958 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 9, 11}

def PredecessorHalfFin13Atom1959 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 9, 12}

def PredecessorHalfFin13Atom1960 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 10, 11}

def PredecessorHalfFin13Atom1961 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 10, 12}

def PredecessorHalfFin13Atom1962 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 8, 11, 12}

def PredecessorHalfFin13Atom1963 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 10, 11}

def PredecessorHalfFin13Atom1964 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 10, 12}

def PredecessorHalfFin13Atom1965 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 9, 11, 12}

def PredecessorHalfFin13Atom1966 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 4, 10, 11, 12}

def PredecessorHalfFin13Atom1967 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 8}

def PredecessorHalfFin13Atom1968 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 9}

def PredecessorHalfFin13Atom1969 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 10}

def PredecessorHalfFin13Atom1970 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 11}

def PredecessorHalfFin13Atom1971 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 7, 12}

def PredecessorHalfFin13Atom1972 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 9}

def PredecessorHalfFin13Atom1973 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 10}

def PredecessorHalfFin13Atom1974 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 11}

def PredecessorHalfFin13Atom1975 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 8, 12}

def PredecessorHalfFin13Atom1976 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 10}

def PredecessorHalfFin13Atom1977 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 11}

def PredecessorHalfFin13Atom1978 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 9, 12}

def PredecessorHalfFin13Atom1979 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 10, 11}

def PredecessorHalfFin13Atom1980 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 10, 12}

def PredecessorHalfFin13Atom1981 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 6, 11, 12}

def PredecessorHalfFin13Atom1982 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 9}

def PredecessorHalfFin13Atom1983 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 10}

def PredecessorHalfFin13Atom1984 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 11}

def PredecessorHalfFin13Atom1985 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 8, 12}

def PredecessorHalfFin13Atom1986 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 10}

def PredecessorHalfFin13Atom1987 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 11}

def PredecessorHalfFin13Atom1988 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 9, 12}

def PredecessorHalfFin13Atom1989 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 10, 11}

def PredecessorHalfFin13Atom1990 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 10, 12}

def PredecessorHalfFin13Atom1991 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 7, 11, 12}

def PredecessorHalfFin13Atom1992 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 9, 10}

def PredecessorHalfFin13Atom1993 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 9, 11}

def PredecessorHalfFin13Atom1994 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 9, 12}

def PredecessorHalfFin13Atom1995 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 10, 11}

def PredecessorHalfFin13Atom1996 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 10, 12}

def PredecessorHalfFin13Atom1997 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 8, 11, 12}

def PredecessorHalfFin13Atom1998 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 10, 11}

def PredecessorHalfFin13Atom1999 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 10, 12}

def PredecessorHalfFin13Atom2000 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 9, 11, 12}

def PredecessorHalfFin13Atom2001 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 5, 10, 11, 12}

def PredecessorHalfFin13Atom2002 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 9}

def PredecessorHalfFin13Atom2003 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 10}

def PredecessorHalfFin13Atom2004 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 11}

def PredecessorHalfFin13Atom2005 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 8, 12}

def PredecessorHalfFin13Atom2006 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 10}

def PredecessorHalfFin13Atom2007 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 11}

def PredecessorHalfFin13Atom2008 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 9, 12}

def PredecessorHalfFin13Atom2009 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 10, 11}

def PredecessorHalfFin13Atom2010 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 10, 12}

def PredecessorHalfFin13Atom2011 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 7, 11, 12}

def PredecessorHalfFin13Atom2012 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 9, 10}

def PredecessorHalfFin13Atom2013 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 9, 11}

def PredecessorHalfFin13Atom2014 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 9, 12}

def PredecessorHalfFin13Atom2015 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 10, 11}

def PredecessorHalfFin13Atom2016 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 10, 12}

def PredecessorHalfFin13Atom2017 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 8, 11, 12}

def PredecessorHalfFin13Atom2018 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 10, 11}

def PredecessorHalfFin13Atom2019 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 10, 12}

def PredecessorHalfFin13Atom2020 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 9, 11, 12}

def PredecessorHalfFin13Atom2021 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 6, 10, 11, 12}

def PredecessorHalfFin13Atom2022 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 9, 10}

def PredecessorHalfFin13Atom2023 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 9, 11}

def PredecessorHalfFin13Atom2024 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 9, 12}

def PredecessorHalfFin13Atom2025 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 10, 11}

def PredecessorHalfFin13Atom2026 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 10, 12}

def PredecessorHalfFin13Atom2027 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 7, 8, 11, 12}

def PredecessorHalfFin13Atom2028 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 10, 11}

def PredecessorHalfFin13Atom2029 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 10, 12}

def PredecessorHalfFin13Atom2030 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 7, 9, 11, 12}

def PredecessorHalfFin13Atom2031 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 7, 10, 11, 12}

def PredecessorHalfFin13Atom2032 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 8, 9, 10, 11}

def PredecessorHalfFin13Atom2033 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 8, 9, 10, 12}

def PredecessorHalfFin13Atom2034 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 8, 9, 11, 12}

def PredecessorHalfFin13Atom2035 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 8, 10, 11, 12}

def PredecessorHalfFin13Atom2036 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {2, 9, 10, 11, 12}

def PredecessorHalfFin13Atom2037 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 7}

def PredecessorHalfFin13Atom2038 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 8}

def PredecessorHalfFin13Atom2039 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 9}

def PredecessorHalfFin13Atom2040 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 10}

def PredecessorHalfFin13Atom2041 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 11}

def PredecessorHalfFin13Atom2042 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 6, 12}

def PredecessorHalfFin13Atom2043 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 8}

def PredecessorHalfFin13Atom2044 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 9}

def PredecessorHalfFin13Atom2045 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 10}

def PredecessorHalfFin13Atom2046 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 11}

def PredecessorHalfFin13Atom2047 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 7, 12}

def PredecessorHalfFin13Atom2048 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 9}

def PredecessorHalfFin13Atom2049 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 10}

def PredecessorHalfFin13Atom2050 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 11}

def PredecessorHalfFin13Atom2051 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 8, 12}

def PredecessorHalfFin13Atom2052 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 10}

def PredecessorHalfFin13Atom2053 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 11}

def PredecessorHalfFin13Atom2054 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 9, 12}

def PredecessorHalfFin13Atom2055 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 10, 11}

def PredecessorHalfFin13Atom2056 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 10, 12}

def PredecessorHalfFin13Atom2057 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 5, 11, 12}

def PredecessorHalfFin13Atom2058 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 8}

def PredecessorHalfFin13Atom2059 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 9}

def PredecessorHalfFin13Atom2060 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 10}

def PredecessorHalfFin13Atom2061 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 11}

def PredecessorHalfFin13Atom2062 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 7, 12}

def PredecessorHalfFin13Atom2063 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 9}

def PredecessorHalfFin13Atom2064 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 10}

def PredecessorHalfFin13Atom2065 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 11}

def PredecessorHalfFin13Atom2066 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 8, 12}

def PredecessorHalfFin13Atom2067 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 10}

def PredecessorHalfFin13Atom2068 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 11}

def PredecessorHalfFin13Atom2069 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 9, 12}

def PredecessorHalfFin13Atom2070 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 10, 11}

def PredecessorHalfFin13Atom2071 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 10, 12}

def PredecessorHalfFin13Atom2072 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 6, 11, 12}

def PredecessorHalfFin13Atom2073 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 9}

def PredecessorHalfFin13Atom2074 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 10}

def PredecessorHalfFin13Atom2075 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 11}

def PredecessorHalfFin13Atom2076 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 8, 12}

def PredecessorHalfFin13Atom2077 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 10}

def PredecessorHalfFin13Atom2078 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 11}

def PredecessorHalfFin13Atom2079 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 9, 12}

def PredecessorHalfFin13Atom2080 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 10, 11}

def PredecessorHalfFin13Atom2081 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 10, 12}

def PredecessorHalfFin13Atom2082 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 7, 11, 12}

def PredecessorHalfFin13Atom2083 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 10}

def PredecessorHalfFin13Atom2084 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 11}

def PredecessorHalfFin13Atom2085 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 9, 12}

def PredecessorHalfFin13Atom2086 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 10, 11}

def PredecessorHalfFin13Atom2087 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 10, 12}

def PredecessorHalfFin13Atom2088 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 8, 11, 12}

def PredecessorHalfFin13Atom2089 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 10, 11}

def PredecessorHalfFin13Atom2090 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 10, 12}

def PredecessorHalfFin13Atom2091 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 9, 11, 12}

def PredecessorHalfFin13Atom2092 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 4, 10, 11, 12}

def PredecessorHalfFin13Atom2093 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 8}

def PredecessorHalfFin13Atom2094 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 9}

def PredecessorHalfFin13Atom2095 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 10}

def PredecessorHalfFin13Atom2096 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 11}

def PredecessorHalfFin13Atom2097 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 7, 12}

def PredecessorHalfFin13Atom2098 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 9}

def PredecessorHalfFin13Atom2099 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 10}

def PredecessorHalfFin13Atom2100 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 11}

def PredecessorHalfFin13Atom2101 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 8, 12}

def PredecessorHalfFin13Atom2102 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 10}

def PredecessorHalfFin13Atom2103 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 11}

def PredecessorHalfFin13Atom2104 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 9, 12}

def PredecessorHalfFin13Atom2105 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 10, 11}

def PredecessorHalfFin13Atom2106 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 10, 12}

def PredecessorHalfFin13Atom2107 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 6, 11, 12}

def PredecessorHalfFin13Atom2108 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 9}

def PredecessorHalfFin13Atom2109 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 10}

def PredecessorHalfFin13Atom2110 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 11}

def PredecessorHalfFin13Atom2111 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 8, 12}

def PredecessorHalfFin13Atom2112 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 10}

def PredecessorHalfFin13Atom2113 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 11}

def PredecessorHalfFin13Atom2114 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 9, 12}

def PredecessorHalfFin13Atom2115 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 10, 11}

def PredecessorHalfFin13Atom2116 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 10, 12}

def PredecessorHalfFin13Atom2117 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 7, 11, 12}

def PredecessorHalfFin13Atom2118 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 10}

def PredecessorHalfFin13Atom2119 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 11}

def PredecessorHalfFin13Atom2120 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 9, 12}

def PredecessorHalfFin13Atom2121 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 10, 11}

def PredecessorHalfFin13Atom2122 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 10, 12}

def PredecessorHalfFin13Atom2123 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 8, 11, 12}

def PredecessorHalfFin13Atom2124 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 10, 11}

def PredecessorHalfFin13Atom2125 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 10, 12}

def PredecessorHalfFin13Atom2126 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 9, 11, 12}

def PredecessorHalfFin13Atom2127 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 5, 10, 11, 12}

def PredecessorHalfFin13Atom2128 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 9}

def PredecessorHalfFin13Atom2129 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 10}

def PredecessorHalfFin13Atom2130 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 11}

def PredecessorHalfFin13Atom2131 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 8, 12}

def PredecessorHalfFin13Atom2132 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 10}

def PredecessorHalfFin13Atom2133 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 11}

def PredecessorHalfFin13Atom2134 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 9, 12}

def PredecessorHalfFin13Atom2135 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 10, 11}

def PredecessorHalfFin13Atom2136 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 10, 12}

def PredecessorHalfFin13Atom2137 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 7, 11, 12}

def PredecessorHalfFin13Atom2138 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 10}

def PredecessorHalfFin13Atom2139 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 11}

def PredecessorHalfFin13Atom2140 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 9, 12}

def PredecessorHalfFin13Atom2141 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 10, 11}

def PredecessorHalfFin13Atom2142 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 10, 12}

def PredecessorHalfFin13Atom2143 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 8, 11, 12}

def PredecessorHalfFin13Atom2144 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 10, 11}

def PredecessorHalfFin13Atom2145 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 10, 12}

def PredecessorHalfFin13Atom2146 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 9, 11, 12}

def PredecessorHalfFin13Atom2147 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 6, 10, 11, 12}

def PredecessorHalfFin13Atom2148 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 9, 10}

def PredecessorHalfFin13Atom2149 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 9, 11}

def PredecessorHalfFin13Atom2150 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 9, 12}

def PredecessorHalfFin13Atom2151 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 10, 11}

def PredecessorHalfFin13Atom2152 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 10, 12}

def PredecessorHalfFin13Atom2153 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 7, 8, 11, 12}

def PredecessorHalfFin13Atom2154 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 10, 11}

def PredecessorHalfFin13Atom2155 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 10, 12}

def PredecessorHalfFin13Atom2156 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 7, 9, 11, 12}

def PredecessorHalfFin13Atom2157 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 7, 10, 11, 12}

def PredecessorHalfFin13Atom2158 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 8, 9, 10, 11}

def PredecessorHalfFin13Atom2159 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 8, 9, 10, 12}

def PredecessorHalfFin13Atom2160 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 8, 9, 11, 12}

def PredecessorHalfFin13Atom2161 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 8, 10, 11, 12}

def PredecessorHalfFin13Atom2162 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {3, 9, 10, 11, 12}

def PredecessorHalfFin13Atom2163 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 8}

def PredecessorHalfFin13Atom2164 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 9}

def PredecessorHalfFin13Atom2165 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 10}

def PredecessorHalfFin13Atom2166 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 11}

def PredecessorHalfFin13Atom2167 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 7, 12}

def PredecessorHalfFin13Atom2168 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 9}

def PredecessorHalfFin13Atom2169 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 10}

def PredecessorHalfFin13Atom2170 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 11}

def PredecessorHalfFin13Atom2171 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 8, 12}

def PredecessorHalfFin13Atom2172 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 10}

def PredecessorHalfFin13Atom2173 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 11}

def PredecessorHalfFin13Atom2174 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 9, 12}

def PredecessorHalfFin13Atom2175 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 10, 11}

def PredecessorHalfFin13Atom2176 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 10, 12}

def PredecessorHalfFin13Atom2177 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 6, 11, 12}

def PredecessorHalfFin13Atom2178 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 9}

def PredecessorHalfFin13Atom2179 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 10}

def PredecessorHalfFin13Atom2180 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 11}

def PredecessorHalfFin13Atom2181 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 8, 12}

def PredecessorHalfFin13Atom2182 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 10}

def PredecessorHalfFin13Atom2183 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 11}

def PredecessorHalfFin13Atom2184 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 9, 12}

def PredecessorHalfFin13Atom2185 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 10, 11}

def PredecessorHalfFin13Atom2186 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 10, 12}

def PredecessorHalfFin13Atom2187 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 7, 11, 12}

def PredecessorHalfFin13Atom2188 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 10}

def PredecessorHalfFin13Atom2189 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 11}

def PredecessorHalfFin13Atom2190 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 9, 12}

def PredecessorHalfFin13Atom2191 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 10, 11}

def PredecessorHalfFin13Atom2192 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 10, 12}

def PredecessorHalfFin13Atom2193 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 8, 11, 12}

def PredecessorHalfFin13Atom2194 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 10, 11}

def PredecessorHalfFin13Atom2195 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 10, 12}

def PredecessorHalfFin13Atom2196 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 9, 11, 12}

def PredecessorHalfFin13Atom2197 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 5, 10, 11, 12}

def PredecessorHalfFin13Atom2198 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 9}

def PredecessorHalfFin13Atom2199 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 10}

def PredecessorHalfFin13Atom2200 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 11}

def PredecessorHalfFin13Atom2201 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 8, 12}

def PredecessorHalfFin13Atom2202 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 10}

def PredecessorHalfFin13Atom2203 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 11}

def PredecessorHalfFin13Atom2204 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 9, 12}

def PredecessorHalfFin13Atom2205 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 10, 11}

def PredecessorHalfFin13Atom2206 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 10, 12}

def PredecessorHalfFin13Atom2207 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 7, 11, 12}

def PredecessorHalfFin13Atom2208 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 10}

def PredecessorHalfFin13Atom2209 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 11}

def PredecessorHalfFin13Atom2210 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 9, 12}

def PredecessorHalfFin13Atom2211 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 10, 11}

def PredecessorHalfFin13Atom2212 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 10, 12}

def PredecessorHalfFin13Atom2213 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 8, 11, 12}

def PredecessorHalfFin13Atom2214 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 10, 11}

def PredecessorHalfFin13Atom2215 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 10, 12}

def PredecessorHalfFin13Atom2216 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 9, 11, 12}

def PredecessorHalfFin13Atom2217 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 6, 10, 11, 12}

def PredecessorHalfFin13Atom2218 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 10}

def PredecessorHalfFin13Atom2219 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 11}

def PredecessorHalfFin13Atom2220 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 9, 12}

def PredecessorHalfFin13Atom2221 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 10, 11}

def PredecessorHalfFin13Atom2222 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 10, 12}

def PredecessorHalfFin13Atom2223 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 7, 8, 11, 12}

def PredecessorHalfFin13Atom2224 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 10, 11}

def PredecessorHalfFin13Atom2225 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 10, 12}

def PredecessorHalfFin13Atom2226 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 7, 9, 11, 12}

def PredecessorHalfFin13Atom2227 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 7, 10, 11, 12}

def PredecessorHalfFin13Atom2228 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 8, 9, 10, 11}

def PredecessorHalfFin13Atom2229 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 8, 9, 10, 12}

def PredecessorHalfFin13Atom2230 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 8, 9, 11, 12}

def PredecessorHalfFin13Atom2231 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 8, 10, 11, 12}

def PredecessorHalfFin13Atom2232 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {4, 9, 10, 11, 12}

def PredecessorHalfFin13Atom2233 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 9}

def PredecessorHalfFin13Atom2234 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 10}

def PredecessorHalfFin13Atom2235 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 11}

def PredecessorHalfFin13Atom2236 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 8, 12}

def PredecessorHalfFin13Atom2237 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 10}

def PredecessorHalfFin13Atom2238 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 11}

def PredecessorHalfFin13Atom2239 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 9, 12}

def PredecessorHalfFin13Atom2240 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 10, 11}

def PredecessorHalfFin13Atom2241 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 10, 12}

def PredecessorHalfFin13Atom2242 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 7, 11, 12}

def PredecessorHalfFin13Atom2243 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 10}

def PredecessorHalfFin13Atom2244 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 11}

def PredecessorHalfFin13Atom2245 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 9, 12}

def PredecessorHalfFin13Atom2246 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 10, 11}

def PredecessorHalfFin13Atom2247 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 10, 12}

def PredecessorHalfFin13Atom2248 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 8, 11, 12}

def PredecessorHalfFin13Atom2249 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 10, 11}

def PredecessorHalfFin13Atom2250 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 10, 12}

def PredecessorHalfFin13Atom2251 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 9, 11, 12}

def PredecessorHalfFin13Atom2252 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 6, 10, 11, 12}

def PredecessorHalfFin13Atom2253 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 10}

def PredecessorHalfFin13Atom2254 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 11}

def PredecessorHalfFin13Atom2255 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 9, 12}

def PredecessorHalfFin13Atom2256 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 10, 11}

def PredecessorHalfFin13Atom2257 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 10, 12}

def PredecessorHalfFin13Atom2258 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 7, 8, 11, 12}

def PredecessorHalfFin13Atom2259 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 10, 11}

def PredecessorHalfFin13Atom2260 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 10, 12}

def PredecessorHalfFin13Atom2261 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 7, 9, 11, 12}

def PredecessorHalfFin13Atom2262 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 7, 10, 11, 12}

def PredecessorHalfFin13Atom2263 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 8, 9, 10, 11}

def PredecessorHalfFin13Atom2264 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 8, 9, 10, 12}

def PredecessorHalfFin13Atom2265 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 8, 9, 11, 12}

def PredecessorHalfFin13Atom2266 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 8, 10, 11, 12}

def PredecessorHalfFin13Atom2267 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {5, 9, 10, 11, 12}

def PredecessorHalfFin13Atom2268 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 10}

def PredecessorHalfFin13Atom2269 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 11}

def PredecessorHalfFin13Atom2270 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 9, 12}

def PredecessorHalfFin13Atom2271 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 10, 11}

def PredecessorHalfFin13Atom2272 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 10, 12}

def PredecessorHalfFin13Atom2273 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 7, 8, 11, 12}

def PredecessorHalfFin13Atom2274 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 10, 11}

def PredecessorHalfFin13Atom2275 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 10, 12}

def PredecessorHalfFin13Atom2276 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 7, 9, 11, 12}

def PredecessorHalfFin13Atom2277 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 7, 10, 11, 12}

def PredecessorHalfFin13Atom2278 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 8, 9, 10, 11}

def PredecessorHalfFin13Atom2279 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 8, 9, 10, 12}

def PredecessorHalfFin13Atom2280 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 8, 9, 11, 12}

def PredecessorHalfFin13Atom2281 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 8, 10, 11, 12}

def PredecessorHalfFin13Atom2282 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {6, 9, 10, 11, 12}

def PredecessorHalfFin13Atom2283 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {7, 8, 9, 10, 11}

def PredecessorHalfFin13Atom2284 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {7, 8, 9, 10, 12}

def PredecessorHalfFin13Atom2285 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {7, 8, 9, 11, 12}

def PredecessorHalfFin13Atom2286 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {7, 8, 10, 11, 12}

def PredecessorHalfFin13Atom2287 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {7, 9, 10, 11, 12}

def PredecessorHalfFin13Atom2288 (chi : TripleColoring 13) : Prop :=
  IsStrongPolygonSet chi {8, 9, 10, 11, 12}

end ErdosSzekeres

end
