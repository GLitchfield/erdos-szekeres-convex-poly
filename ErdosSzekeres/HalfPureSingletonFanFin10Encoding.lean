module

public import ErdosSzekeres.HalfPureSingletonFan

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-- The exact bounded singleton-fan conclusion certified at Fin 10. -/
def HalfPureSingletonFanFin10Conclusion (χ : TripleColoring 10) : Prop :=
  ∃ side : Finset (Fin 10), ∃ pivot : Fin 10,
    pivot ∉ side ∧
    10 ≤ 2 * side.card ∧
    ((HasDeepBelowSplit χ side {pivot} ∧
        ∀ polygon : Finset (Fin 10),
          polygon ⊆ side → polygon.card = 5 →
            IsStrongPolygonSet χ polygon → IsCupSet χ polygon) ∨
     (HasDeepBelowSplit χ {pivot} side ∧
        ∀ polygon : Finset (Fin 10),
          polygon ⊆ side → polygon.card = 5 →
            IsStrongPolygonSet χ polygon → IsCapSet χ polygon))

def HalfPureSingletonFanFin10StrongQuad (χ : TripleColoring 10)
    (a b c d : Fin 10) (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=
  χ ⟨a, b, c, hab, hbc⟩ = χ ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
    χ ⟨a, c, d, hab.trans hbc, hcd⟩ = χ ⟨b, c, d, hbc, hcd⟩

def HalfPureSingletonFanFin10Atom0009 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0011 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0012 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0013 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0014 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0015 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0017 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0018 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0019 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0020 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0021 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0027 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0028 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0029 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0030 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0031 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0032 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0033 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0034 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0035 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0036 (χ : TripleColoring 10) : Prop :=
  χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0065 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0066 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0067 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0068 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0069 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0070 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0071 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0072 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0073 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0074 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0075 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0076 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0077 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0078 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0079 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0080 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0081 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0082 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0083 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0084 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0085 (χ : TripleColoring 10) : Prop :=
  χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0086 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0087 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0088 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0089 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0090 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0091 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0092 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0093 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0094 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0095 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0096 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0097 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0098 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0099 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0100 (χ : TripleColoring 10) : Prop :=
  χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0101 (χ : TripleColoring 10) : Prop :=
  χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0102 (χ : TripleColoring 10) : Prop :=
  χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0103 (χ : TripleColoring 10) : Prop :=
  χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0104 (χ : TripleColoring 10) : Prop :=
  χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0105 (χ : TripleColoring 10) : Prop :=
  χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0106 (χ : TripleColoring 10) : Prop :=
  χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0107 (χ : TripleColoring 10) : Prop :=
  χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0108 (χ : TripleColoring 10) : Prop :=
  χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0109 (χ : TripleColoring 10) : Prop :=
  χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0110 (χ : TripleColoring 10) : Prop :=
  χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0111 (χ : TripleColoring 10) : Prop :=
  χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0112 (χ : TripleColoring 10) : Prop :=
  χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0113 (χ : TripleColoring 10) : Prop :=
  χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0114 (χ : TripleColoring 10) : Prop :=
  χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0115 (χ : TripleColoring 10) : Prop :=
  χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0116 (χ : TripleColoring 10) : Prop :=
  χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0117 (χ : TripleColoring 10) : Prop :=
  χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0118 (χ : TripleColoring 10) : Prop :=
  χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0119 (χ : TripleColoring 10) : Prop :=
  χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0120 (χ : TripleColoring 10) : Prop :=
  χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left

def HalfPureSingletonFanFin10Atom0150 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 3 5 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0151 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 3 6 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0152 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 3 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0153 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 3 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0154 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 3 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0160 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 5 6 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0161 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 5 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0162 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 5 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0163 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 5 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0164 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 6 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0165 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 6 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0166 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 6 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0167 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0168 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0169 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 2 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0175 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 3 5 6 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0176 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 3 5 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0177 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 3 5 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0178 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 3 5 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0179 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 3 6 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0180 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 3 6 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0181 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 3 6 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0182 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 3 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0183 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 3 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0184 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 3 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0195 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 5 6 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0196 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 5 6 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0197 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 5 6 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0198 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 5 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0199 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 5 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0200 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 5 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0201 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 6 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0202 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 6 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0203 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 6 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0204 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 0 7 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0261 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 4 5 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0262 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 4 6 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0263 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 4 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0264 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 4 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0265 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 4 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0266 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 5 6 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0267 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 5 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0268 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 5 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0269 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 5 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0270 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 6 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0271 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 6 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0272 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 6 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0273 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0274 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0275 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 3 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0276 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 4 5 6 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0277 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 4 5 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0278 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 4 5 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0279 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 4 5 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0280 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 4 6 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0281 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 4 6 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0282 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 4 6 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0283 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 4 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0284 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 4 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0285 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 4 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0286 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 5 6 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0287 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 5 6 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0288 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 5 6 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0289 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 5 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0290 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 5 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0291 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 5 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0292 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 6 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0293 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 6 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0294 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 6 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0295 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 2 7 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0296 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 4 5 6 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0297 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 4 5 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0298 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 4 5 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0299 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 4 5 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0300 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 4 6 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0301 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 4 6 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0302 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 4 6 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0303 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 4 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0304 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 4 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0305 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 4 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0306 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 5 6 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0307 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 5 6 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0308 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 5 6 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0309 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 5 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0310 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 5 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0311 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 5 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0312 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 6 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0313 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 6 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0314 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 6 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0315 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 3 7 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0316 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 4 5 6 7 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0317 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 4 5 6 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0318 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 4 5 6 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0319 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 4 5 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0320 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 4 5 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0321 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 4 5 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0322 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 4 6 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0323 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 4 6 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0324 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 4 6 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0325 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 4 7 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0326 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 5 6 7 8 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0327 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 5 6 7 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0328 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 5 6 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0329 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 5 7 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0330 (χ : TripleColoring 10) : Prop :=
  HalfPureSingletonFanFin10StrongQuad χ 6 7 8 9 (by decide) (by decide) (by decide)

def HalfPureSingletonFanFin10Atom0392 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 6}

def HalfPureSingletonFanFin10Atom0393 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 7}

def HalfPureSingletonFanFin10Atom0394 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 8}

def HalfPureSingletonFanFin10Atom0395 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 9}

def HalfPureSingletonFanFin10Atom0396 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 6, 7}

def HalfPureSingletonFanFin10Atom0397 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 6, 8}

def HalfPureSingletonFanFin10Atom0398 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 6, 9}

def HalfPureSingletonFanFin10Atom0399 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 7, 8}

def HalfPureSingletonFanFin10Atom0400 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 7, 9}

def HalfPureSingletonFanFin10Atom0401 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 8, 9}

def HalfPureSingletonFanFin10Atom0412 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 6, 7}

def HalfPureSingletonFanFin10Atom0413 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0414 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0415 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0416 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 7, 9}

def HalfPureSingletonFanFin10Atom0417 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 8, 9}

def HalfPureSingletonFanFin10Atom0418 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0419 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0420 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0421 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0432 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 6, 7}

def HalfPureSingletonFanFin10Atom0433 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0434 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0435 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0436 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 7, 9}

def HalfPureSingletonFanFin10Atom0437 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 8, 9}

def HalfPureSingletonFanFin10Atom0438 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0439 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0440 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0441 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0452 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0453 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0454 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0455 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0456 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0527 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 5, 6}

def HalfPureSingletonFanFin10Atom0529 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 5, 8}

def HalfPureSingletonFanFin10Atom0530 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 5, 9}

def HalfPureSingletonFanFin10Atom0531 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 6, 7}

def HalfPureSingletonFanFin10Atom0532 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 6, 8}

def HalfPureSingletonFanFin10Atom0533 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 6, 9}

def HalfPureSingletonFanFin10Atom0534 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 7, 8}

def HalfPureSingletonFanFin10Atom0535 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 7, 9}

def HalfPureSingletonFanFin10Atom0536 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 8, 9}

def HalfPureSingletonFanFin10Atom0537 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 6, 7}

def HalfPureSingletonFanFin10Atom0538 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0539 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0540 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0541 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 7, 9}

def HalfPureSingletonFanFin10Atom0542 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 8, 9}

def HalfPureSingletonFanFin10Atom0543 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0544 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0545 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0546 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0547 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 6, 7}

def HalfPureSingletonFanFin10Atom0548 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0549 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0550 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0551 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 7, 9}

def HalfPureSingletonFanFin10Atom0552 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 8, 9}

def HalfPureSingletonFanFin10Atom0553 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0554 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0555 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0556 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0557 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0558 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0559 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0560 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0561 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0562 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 6, 7}

def HalfPureSingletonFanFin10Atom0563 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0564 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0565 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0566 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 7, 9}

def HalfPureSingletonFanFin10Atom0567 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 8, 9}

def HalfPureSingletonFanFin10Atom0568 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0570 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0571 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0572 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0573 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0574 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0575 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0576 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0577 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0578 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 5, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0579 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0580 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0581 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0582 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {5, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0644 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 6} ∧
    ¬IsCupSet χ {0, 2, 3, 5, 6}

def HalfPureSingletonFanFin10Atom0645 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 7} ∧
    ¬IsCupSet χ {0, 2, 3, 5, 7}

def HalfPureSingletonFanFin10Atom0646 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 8} ∧
    ¬IsCupSet χ {0, 2, 3, 5, 8}

def HalfPureSingletonFanFin10Atom0647 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 9} ∧
    ¬IsCupSet χ {0, 2, 3, 5, 9}

def HalfPureSingletonFanFin10Atom0648 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 6, 7} ∧
    ¬IsCupSet χ {0, 2, 3, 6, 7}

def HalfPureSingletonFanFin10Atom0649 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 6, 8} ∧
    ¬IsCupSet χ {0, 2, 3, 6, 8}

def HalfPureSingletonFanFin10Atom0650 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 6, 9} ∧
    ¬IsCupSet χ {0, 2, 3, 6, 9}

def HalfPureSingletonFanFin10Atom0651 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 7, 8} ∧
    ¬IsCupSet χ {0, 2, 3, 7, 8}

def HalfPureSingletonFanFin10Atom0652 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 7, 9} ∧
    ¬IsCupSet χ {0, 2, 3, 7, 9}

def HalfPureSingletonFanFin10Atom0653 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 8, 9} ∧
    ¬IsCupSet χ {0, 2, 3, 8, 9}

def HalfPureSingletonFanFin10Atom0664 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 6, 7} ∧
    ¬IsCupSet χ {0, 2, 5, 6, 7}

def HalfPureSingletonFanFin10Atom0665 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 6, 8} ∧
    ¬IsCupSet χ {0, 2, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0666 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 6, 9} ∧
    ¬IsCupSet χ {0, 2, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0667 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 7, 8} ∧
    ¬IsCupSet χ {0, 2, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0668 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 7, 9} ∧
    ¬IsCupSet χ {0, 2, 5, 7, 9}

def HalfPureSingletonFanFin10Atom0669 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 8, 9} ∧
    ¬IsCupSet χ {0, 2, 5, 8, 9}

def HalfPureSingletonFanFin10Atom0670 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 6, 7, 8} ∧
    ¬IsCupSet χ {0, 2, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0671 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 6, 7, 9} ∧
    ¬IsCupSet χ {0, 2, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0672 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 6, 8, 9} ∧
    ¬IsCupSet χ {0, 2, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0673 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 7, 8, 9} ∧
    ¬IsCupSet χ {0, 2, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0684 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 6, 7} ∧
    ¬IsCupSet χ {0, 3, 5, 6, 7}

def HalfPureSingletonFanFin10Atom0685 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 6, 8} ∧
    ¬IsCupSet χ {0, 3, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0686 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 6, 9} ∧
    ¬IsCupSet χ {0, 3, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0687 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 7, 8} ∧
    ¬IsCupSet χ {0, 3, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0688 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 7, 9} ∧
    ¬IsCupSet χ {0, 3, 5, 7, 9}

def HalfPureSingletonFanFin10Atom0689 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 8, 9} ∧
    ¬IsCupSet χ {0, 3, 5, 8, 9}

def HalfPureSingletonFanFin10Atom0690 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 6, 7, 8} ∧
    ¬IsCupSet χ {0, 3, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0691 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 6, 7, 9} ∧
    ¬IsCupSet χ {0, 3, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0692 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 6, 8, 9} ∧
    ¬IsCupSet χ {0, 3, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0693 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 7, 8, 9} ∧
    ¬IsCupSet χ {0, 3, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0704 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 6, 7, 8} ∧
    ¬IsCupSet χ {0, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0705 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 6, 7, 9} ∧
    ¬IsCupSet χ {0, 5, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0706 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 6, 8, 9} ∧
    ¬IsCupSet χ {0, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0707 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 7, 8, 9} ∧
    ¬IsCupSet χ {0, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0708 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 6, 7, 8, 9} ∧
    ¬IsCupSet χ {0, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0779 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 5, 6} ∧
    ¬IsCupSet χ {2, 3, 4, 5, 6}

def HalfPureSingletonFanFin10Atom0781 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 5, 8} ∧
    ¬IsCupSet χ {2, 3, 4, 5, 8}

def HalfPureSingletonFanFin10Atom0782 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 5, 9} ∧
    ¬IsCupSet χ {2, 3, 4, 5, 9}

def HalfPureSingletonFanFin10Atom0784 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 6, 8} ∧
    ¬IsCupSet χ {2, 3, 4, 6, 8}

def HalfPureSingletonFanFin10Atom0785 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 6, 9} ∧
    ¬IsCupSet χ {2, 3, 4, 6, 9}

def HalfPureSingletonFanFin10Atom0786 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 7, 8} ∧
    ¬IsCupSet χ {2, 3, 4, 7, 8}

def HalfPureSingletonFanFin10Atom0787 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 7, 9} ∧
    ¬IsCupSet χ {2, 3, 4, 7, 9}

def HalfPureSingletonFanFin10Atom0788 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 8, 9} ∧
    ¬IsCupSet χ {2, 3, 4, 8, 9}

def HalfPureSingletonFanFin10Atom0789 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 6, 7} ∧
    ¬IsCupSet χ {2, 3, 5, 6, 7}

def HalfPureSingletonFanFin10Atom0790 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 6, 8} ∧
    ¬IsCupSet χ {2, 3, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0791 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 6, 9} ∧
    ¬IsCupSet χ {2, 3, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0792 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 7, 8} ∧
    ¬IsCupSet χ {2, 3, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0793 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 7, 9} ∧
    ¬IsCupSet χ {2, 3, 5, 7, 9}

def HalfPureSingletonFanFin10Atom0794 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 8, 9} ∧
    ¬IsCupSet χ {2, 3, 5, 8, 9}

def HalfPureSingletonFanFin10Atom0795 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 6, 7, 8} ∧
    ¬IsCupSet χ {2, 3, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0796 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 6, 7, 9} ∧
    ¬IsCupSet χ {2, 3, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0797 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 6, 8, 9} ∧
    ¬IsCupSet χ {2, 3, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0798 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 7, 8, 9} ∧
    ¬IsCupSet χ {2, 3, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0799 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 6, 7} ∧
    ¬IsCupSet χ {2, 4, 5, 6, 7}

def HalfPureSingletonFanFin10Atom0800 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 6, 8} ∧
    ¬IsCupSet χ {2, 4, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0801 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 6, 9} ∧
    ¬IsCupSet χ {2, 4, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0802 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 7, 8} ∧
    ¬IsCupSet χ {2, 4, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0805 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 6, 7, 8} ∧
    ¬IsCupSet χ {2, 4, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0806 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 6, 7, 9} ∧
    ¬IsCupSet χ {2, 4, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0807 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 6, 8, 9} ∧
    ¬IsCupSet χ {2, 4, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0808 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 7, 8, 9} ∧
    ¬IsCupSet χ {2, 4, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0809 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 6, 7, 8} ∧
    ¬IsCupSet χ {2, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0810 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 6, 7, 9} ∧
    ¬IsCupSet χ {2, 5, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0811 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 6, 8, 9} ∧
    ¬IsCupSet χ {2, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0812 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 7, 8, 9} ∧
    ¬IsCupSet χ {2, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0813 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 6, 7, 8, 9} ∧
    ¬IsCupSet χ {2, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0815 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 6, 8} ∧
    ¬IsCupSet χ {3, 4, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0816 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 6, 9} ∧
    ¬IsCupSet χ {3, 4, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0817 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 7, 8} ∧
    ¬IsCupSet χ {3, 4, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0818 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 7, 9} ∧
    ¬IsCupSet χ {3, 4, 5, 7, 9}

def HalfPureSingletonFanFin10Atom0819 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 8, 9} ∧
    ¬IsCupSet χ {3, 4, 5, 8, 9}

def HalfPureSingletonFanFin10Atom0820 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 6, 7, 8} ∧
    ¬IsCupSet χ {3, 4, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0822 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 6, 8, 9} ∧
    ¬IsCupSet χ {3, 4, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0823 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 7, 8, 9} ∧
    ¬IsCupSet χ {3, 4, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0824 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 6, 7, 8} ∧
    ¬IsCupSet χ {3, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0825 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 6, 7, 9} ∧
    ¬IsCupSet χ {3, 5, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0826 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 6, 8, 9} ∧
    ¬IsCupSet χ {3, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0827 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 7, 8, 9} ∧
    ¬IsCupSet χ {3, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0828 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 6, 7, 8, 9} ∧
    ¬IsCupSet χ {3, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0829 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 5, 6, 7, 8} ∧
    ¬IsCupSet χ {4, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0830 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 5, 6, 7, 9} ∧
    ¬IsCupSet χ {4, 5, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0831 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 5, 6, 8, 9} ∧
    ¬IsCupSet χ {4, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0832 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 5, 7, 8, 9} ∧
    ¬IsCupSet χ {4, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0833 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 6, 7, 8, 9} ∧
    ¬IsCupSet χ {4, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0896 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 6} ∧
    ¬IsCapSet χ {0, 2, 3, 5, 6}

def HalfPureSingletonFanFin10Atom0897 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 7} ∧
    ¬IsCapSet χ {0, 2, 3, 5, 7}

def HalfPureSingletonFanFin10Atom0898 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 8} ∧
    ¬IsCapSet χ {0, 2, 3, 5, 8}

def HalfPureSingletonFanFin10Atom0899 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 5, 9} ∧
    ¬IsCapSet χ {0, 2, 3, 5, 9}

def HalfPureSingletonFanFin10Atom0900 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 6, 7} ∧
    ¬IsCapSet χ {0, 2, 3, 6, 7}

def HalfPureSingletonFanFin10Atom0901 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 6, 8} ∧
    ¬IsCapSet χ {0, 2, 3, 6, 8}

def HalfPureSingletonFanFin10Atom0902 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 6, 9} ∧
    ¬IsCapSet χ {0, 2, 3, 6, 9}

def HalfPureSingletonFanFin10Atom0903 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 7, 8} ∧
    ¬IsCapSet χ {0, 2, 3, 7, 8}

def HalfPureSingletonFanFin10Atom0904 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 7, 9} ∧
    ¬IsCapSet χ {0, 2, 3, 7, 9}

def HalfPureSingletonFanFin10Atom0905 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 3, 8, 9} ∧
    ¬IsCapSet χ {0, 2, 3, 8, 9}

def HalfPureSingletonFanFin10Atom0916 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 6, 7} ∧
    ¬IsCapSet χ {0, 2, 5, 6, 7}

def HalfPureSingletonFanFin10Atom0917 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 6, 8} ∧
    ¬IsCapSet χ {0, 2, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0918 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 6, 9} ∧
    ¬IsCapSet χ {0, 2, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0919 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 7, 8} ∧
    ¬IsCapSet χ {0, 2, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0920 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 7, 9} ∧
    ¬IsCapSet χ {0, 2, 5, 7, 9}

def HalfPureSingletonFanFin10Atom0921 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 5, 8, 9} ∧
    ¬IsCapSet χ {0, 2, 5, 8, 9}

def HalfPureSingletonFanFin10Atom0922 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 6, 7, 8} ∧
    ¬IsCapSet χ {0, 2, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0923 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 6, 7, 9} ∧
    ¬IsCapSet χ {0, 2, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0924 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 6, 8, 9} ∧
    ¬IsCapSet χ {0, 2, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0925 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 2, 7, 8, 9} ∧
    ¬IsCapSet χ {0, 2, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0936 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 6, 7} ∧
    ¬IsCapSet χ {0, 3, 5, 6, 7}

def HalfPureSingletonFanFin10Atom0937 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 6, 8} ∧
    ¬IsCapSet χ {0, 3, 5, 6, 8}

def HalfPureSingletonFanFin10Atom0938 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 6, 9} ∧
    ¬IsCapSet χ {0, 3, 5, 6, 9}

def HalfPureSingletonFanFin10Atom0939 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 7, 8} ∧
    ¬IsCapSet χ {0, 3, 5, 7, 8}

def HalfPureSingletonFanFin10Atom0940 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 7, 9} ∧
    ¬IsCapSet χ {0, 3, 5, 7, 9}

def HalfPureSingletonFanFin10Atom0941 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 5, 8, 9} ∧
    ¬IsCapSet χ {0, 3, 5, 8, 9}

def HalfPureSingletonFanFin10Atom0942 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 6, 7, 8} ∧
    ¬IsCapSet χ {0, 3, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0943 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 6, 7, 9} ∧
    ¬IsCapSet χ {0, 3, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0944 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 6, 8, 9} ∧
    ¬IsCapSet χ {0, 3, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0945 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 3, 7, 8, 9} ∧
    ¬IsCapSet χ {0, 3, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0956 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 6, 7, 8} ∧
    ¬IsCapSet χ {0, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom0957 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 6, 7, 9} ∧
    ¬IsCapSet χ {0, 5, 6, 7, 9}

def HalfPureSingletonFanFin10Atom0958 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 6, 8, 9} ∧
    ¬IsCapSet χ {0, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom0959 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 5, 7, 8, 9} ∧
    ¬IsCapSet χ {0, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom0960 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {0, 6, 7, 8, 9} ∧
    ¬IsCapSet χ {0, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom1031 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 5, 6} ∧
    ¬IsCapSet χ {2, 3, 4, 5, 6}

def HalfPureSingletonFanFin10Atom1033 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 5, 8} ∧
    ¬IsCapSet χ {2, 3, 4, 5, 8}

def HalfPureSingletonFanFin10Atom1035 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 6, 7} ∧
    ¬IsCapSet χ {2, 3, 4, 6, 7}

def HalfPureSingletonFanFin10Atom1036 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 6, 8} ∧
    ¬IsCapSet χ {2, 3, 4, 6, 8}

def HalfPureSingletonFanFin10Atom1038 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 7, 8} ∧
    ¬IsCapSet χ {2, 3, 4, 7, 8}

def HalfPureSingletonFanFin10Atom1039 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 4, 7, 9} ∧
    ¬IsCapSet χ {2, 3, 4, 7, 9}

def HalfPureSingletonFanFin10Atom1041 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 6, 7} ∧
    ¬IsCapSet χ {2, 3, 5, 6, 7}

def HalfPureSingletonFanFin10Atom1042 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 6, 8} ∧
    ¬IsCapSet χ {2, 3, 5, 6, 8}

def HalfPureSingletonFanFin10Atom1043 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 6, 9} ∧
    ¬IsCapSet χ {2, 3, 5, 6, 9}

def HalfPureSingletonFanFin10Atom1044 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 7, 8} ∧
    ¬IsCapSet χ {2, 3, 5, 7, 8}

def HalfPureSingletonFanFin10Atom1045 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 7, 9} ∧
    ¬IsCapSet χ {2, 3, 5, 7, 9}

def HalfPureSingletonFanFin10Atom1046 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 5, 8, 9} ∧
    ¬IsCapSet χ {2, 3, 5, 8, 9}

def HalfPureSingletonFanFin10Atom1047 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 6, 7, 8} ∧
    ¬IsCapSet χ {2, 3, 6, 7, 8}

def HalfPureSingletonFanFin10Atom1048 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 6, 7, 9} ∧
    ¬IsCapSet χ {2, 3, 6, 7, 9}

def HalfPureSingletonFanFin10Atom1049 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 6, 8, 9} ∧
    ¬IsCapSet χ {2, 3, 6, 8, 9}

def HalfPureSingletonFanFin10Atom1050 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 3, 7, 8, 9} ∧
    ¬IsCapSet χ {2, 3, 7, 8, 9}

def HalfPureSingletonFanFin10Atom1051 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 6, 7} ∧
    ¬IsCapSet χ {2, 4, 5, 6, 7}

def HalfPureSingletonFanFin10Atom1054 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 7, 8} ∧
    ¬IsCapSet χ {2, 4, 5, 7, 8}

def HalfPureSingletonFanFin10Atom1055 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 7, 9} ∧
    ¬IsCapSet χ {2, 4, 5, 7, 9}

def HalfPureSingletonFanFin10Atom1056 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 5, 8, 9} ∧
    ¬IsCapSet χ {2, 4, 5, 8, 9}

def HalfPureSingletonFanFin10Atom1057 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 6, 7, 8} ∧
    ¬IsCapSet χ {2, 4, 6, 7, 8}

def HalfPureSingletonFanFin10Atom1058 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 6, 7, 9} ∧
    ¬IsCapSet χ {2, 4, 6, 7, 9}

def HalfPureSingletonFanFin10Atom1059 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 6, 8, 9} ∧
    ¬IsCapSet χ {2, 4, 6, 8, 9}

def HalfPureSingletonFanFin10Atom1060 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 4, 7, 8, 9} ∧
    ¬IsCapSet χ {2, 4, 7, 8, 9}

def HalfPureSingletonFanFin10Atom1061 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 6, 7, 8} ∧
    ¬IsCapSet χ {2, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom1062 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 6, 7, 9} ∧
    ¬IsCapSet χ {2, 5, 6, 7, 9}

def HalfPureSingletonFanFin10Atom1063 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 6, 8, 9} ∧
    ¬IsCapSet χ {2, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom1064 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 5, 7, 8, 9} ∧
    ¬IsCapSet χ {2, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom1065 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {2, 6, 7, 8, 9} ∧
    ¬IsCapSet χ {2, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom1066 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 6, 7} ∧
    ¬IsCapSet χ {3, 4, 5, 6, 7}

def HalfPureSingletonFanFin10Atom1067 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 6, 8} ∧
    ¬IsCapSet χ {3, 4, 5, 6, 8}

def HalfPureSingletonFanFin10Atom1068 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 6, 9} ∧
    ¬IsCapSet χ {3, 4, 5, 6, 9}

def HalfPureSingletonFanFin10Atom1069 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 7, 8} ∧
    ¬IsCapSet χ {3, 4, 5, 7, 8}

def HalfPureSingletonFanFin10Atom1070 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 7, 9} ∧
    ¬IsCapSet χ {3, 4, 5, 7, 9}

def HalfPureSingletonFanFin10Atom1071 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 5, 8, 9} ∧
    ¬IsCapSet χ {3, 4, 5, 8, 9}

def HalfPureSingletonFanFin10Atom1072 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 6, 7, 8} ∧
    ¬IsCapSet χ {3, 4, 6, 7, 8}

def HalfPureSingletonFanFin10Atom1074 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 6, 8, 9} ∧
    ¬IsCapSet χ {3, 4, 6, 8, 9}

def HalfPureSingletonFanFin10Atom1075 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 4, 7, 8, 9} ∧
    ¬IsCapSet χ {3, 4, 7, 8, 9}

def HalfPureSingletonFanFin10Atom1076 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 6, 7, 8} ∧
    ¬IsCapSet χ {3, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom1077 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 6, 7, 9} ∧
    ¬IsCapSet χ {3, 5, 6, 7, 9}

def HalfPureSingletonFanFin10Atom1078 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 6, 8, 9} ∧
    ¬IsCapSet χ {3, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom1079 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 5, 7, 8, 9} ∧
    ¬IsCapSet χ {3, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom1080 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {3, 6, 7, 8, 9} ∧
    ¬IsCapSet χ {3, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom1081 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 5, 6, 7, 8} ∧
    ¬IsCapSet χ {4, 5, 6, 7, 8}

def HalfPureSingletonFanFin10Atom1083 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 5, 6, 8, 9} ∧
    ¬IsCapSet χ {4, 5, 6, 8, 9}

def HalfPureSingletonFanFin10Atom1084 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 5, 7, 8, 9} ∧
    ¬IsCapSet χ {4, 5, 7, 8, 9}

def HalfPureSingletonFanFin10Atom1085 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {4, 6, 7, 8, 9} ∧
    ¬IsCapSet χ {4, 6, 7, 8, 9}

def HalfPureSingletonFanFin10Atom1086 (χ : TripleColoring 10) : Prop :=
  IsStrongPolygonSet χ {5, 6, 7, 8, 9} ∧
    ¬IsCapSet χ {5, 6, 7, 8, 9}

theorem halfPureSingletonFanFin10_strongSet_iff_mask0109 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 3, 5, 6} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 5 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 6 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0173 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 3, 5, 7} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 5 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0301 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 3, 5, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 5 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0557 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 3, 5, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 5 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 5)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0205 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 3, 6, 7} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0333 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 3, 6, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0589 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 3, 6, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0397 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 3, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0653 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 3, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0781 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 3, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 3 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 3) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0229 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 5, 6, 7} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0357 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 5, 6, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0613 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 5, 6, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0421 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 5, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0677 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 5, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0805 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 5, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0453 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 6, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0709 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 6, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0837 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 6, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0901 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 2, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 2 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 2 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 2) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0233 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 3, 5, 6, 7} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0361 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 3, 5, 6, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0617 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 3, 5, 6, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0425 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 3, 5, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0681 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 3, 5, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0809 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 3, 5, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0457 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 3, 6, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0713 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 3, 6, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0841 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 3, 6, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0905 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 3, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 3 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 3 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0481 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 5, 6, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0737 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 5, 6, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0865 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 5, 6, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0929 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 5, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0961 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {0, 6, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 0 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 0 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 6 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 0) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 6) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0124 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 4, 5, 6} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 5 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 6 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0316 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 4, 5, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 5 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0572 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 4, 5, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 5 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 5)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0220 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 4, 6, 7} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0348 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 4, 6, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0604 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 4, 6, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0412 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 4, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0668 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 4, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0796 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 4, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 4 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 4) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0236 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 5, 6, 7} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0364 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 5, 6, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0620 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 5, 6, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0428 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 5, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0684 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 5, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0812 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 5, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0460 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 6, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0716 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 6, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0844 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 6, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0908 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 3, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 3 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 3 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 3) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0244 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 4, 5, 6, 7} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0372 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 4, 5, 6, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0628 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 4, 5, 6, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0436 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 4, 5, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0692 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 4, 5, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0820 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 4, 5, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0468 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 4, 6, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0724 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 4, 6, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0852 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 4, 6, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0916 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 4, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 4 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 4 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0484 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 5, 6, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0740 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 5, 6, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0868 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 5, 6, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0932 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 5, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0964 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {2, 6, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 2 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 2 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 6 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 2) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 6) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0248 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 4, 5, 6, 7} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 7 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0376 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 4, 5, 6, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0632 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 4, 5, 6, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 6 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 6)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0440 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 4, 5, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0696 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 4, 5, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0824 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 4, 5, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 5 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 5) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0472 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 4, 6, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 4 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0856 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 4, 6, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 4 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0920 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 4, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 4 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 4 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 4) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0488 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 5, 6, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0744 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 5, 6, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0872 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 5, 6, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0936 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 5, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0968 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {3, 6, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 3 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 3 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 6 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 3) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 6) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0496 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {4, 5, 6, 7, 8} ↔
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 7 8 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0752 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {4, 5, 6, 7, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 7 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 7 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 7)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0880 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {4, 5, 6, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 6 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 6) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0944 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {4, 5, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 4 5 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 5 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 5) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0976 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {4, 6, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 4 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 4 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 6 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 4) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 6) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_strongSet_iff_mask0992 (χ : TripleColoring 10) :
    IsStrongPolygonSet χ {5, 6, 7, 8, 9} ↔
      HalfPureSingletonFanFin10StrongQuad χ 5 6 7 8 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 7 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 6 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 5 7 8 9 (by decide) (by decide) (by decide) ∧
      HalfPureSingletonFanFin10StrongQuad χ 6 7 8 9 (by decide) (by decide) (by decide) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 8)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 7) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 6) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 5) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    · simpa [HalfPureSingletonFanFin10StrongQuad] using h
        (i := 6) (j := 7) (k := 8) (l := 9)
        (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨h0, h1, h2, h3, h4⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
    all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_cupSet_iff_mask0109
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 3, 5, 6} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0173
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 3, 5, 7} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0301
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 3, 5, 8} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0557
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 3, 5, 9} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0205
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 3, 6, 7} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0333
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 3, 6, 8} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0589
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 3, 6, 9} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0397
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 3, 7, 8} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0653
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 3, 7, 9} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0781
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 3, 8, 9} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0229
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 5, 6, 7} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0357
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 5, 6, 8} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0613
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 5, 6, 9} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0421
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 5, 7, 8} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0677
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 5, 7, 9} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0805
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 5, 8, 9} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0453
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 6, 7, 8} ↔
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0709
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 6, 7, 9} ↔
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0837
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 6, 8, 9} ↔
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0901
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 2, 7, 8, 9} ↔
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0233
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 3, 5, 6, 7} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0361
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 3, 5, 6, 8} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0617
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 3, 5, 6, 9} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0425
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 3, 5, 7, 8} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0681
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 3, 5, 7, 9} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0809
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 3, 5, 8, 9} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0457
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 3, 6, 7, 8} ↔
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0713
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 3, 6, 7, 9} ↔
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0841
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 3, 6, 8, 9} ↔
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0905
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 3, 7, 8, 9} ↔
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0481
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 5, 6, 7, 8} ↔
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0737
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 5, 6, 7, 9} ↔
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0865
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 5, 6, 8, 9} ↔
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0929
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 5, 7, 8, 9} ↔
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0961
    (χ : TripleColoring 10) :
    IsCupSet χ {0, 6, 7, 8, 9} ↔
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0124
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 4, 5, 6} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0316
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 4, 5, 8} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0572
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 4, 5, 9} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0348
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 4, 6, 8} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0604
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 4, 6, 9} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0412
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 4, 7, 8} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0668
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 4, 7, 9} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0796
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 4, 8, 9} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0236
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 5, 6, 7} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0364
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 5, 6, 8} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0620
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 5, 6, 9} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0428
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 5, 7, 8} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0684
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 5, 7, 9} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0812
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 5, 8, 9} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0460
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 6, 7, 8} ↔
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0716
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 6, 7, 9} ↔
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0844
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 6, 8, 9} ↔
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0908
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 3, 7, 8, 9} ↔
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0244
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 4, 5, 6, 7} ↔
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0372
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 4, 5, 6, 8} ↔
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0628
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 4, 5, 6, 9} ↔
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0436
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 4, 5, 7, 8} ↔
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0468
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 4, 6, 7, 8} ↔
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0724
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 4, 6, 7, 9} ↔
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0852
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 4, 6, 8, 9} ↔
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0916
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 4, 7, 8, 9} ↔
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0484
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 5, 6, 7, 8} ↔
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0740
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 5, 6, 7, 9} ↔
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0868
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 5, 6, 8, 9} ↔
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0932
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 5, 7, 8, 9} ↔
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0964
    (χ : TripleColoring 10) :
    IsCupSet χ {2, 6, 7, 8, 9} ↔
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0376
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 4, 5, 6, 8} ↔
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0632
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 4, 5, 6, 9} ↔
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0440
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 4, 5, 7, 8} ↔
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0696
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 4, 5, 7, 9} ↔
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0824
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 4, 5, 8, 9} ↔
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0472
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 4, 6, 7, 8} ↔
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0856
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 4, 6, 8, 9} ↔
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0920
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 4, 7, 8, 9} ↔
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0488
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 5, 6, 7, 8} ↔
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0744
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 5, 6, 7, 9} ↔
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0872
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 5, 6, 8, 9} ↔
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0936
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 5, 7, 8, 9} ↔
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0968
    (χ : TripleColoring 10) :
    IsCupSet χ {3, 6, 7, 8, 9} ↔
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0496
    (χ : TripleColoring 10) :
    IsCupSet χ {4, 5, 6, 7, 8} ↔
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0752
    (χ : TripleColoring 10) :
    IsCupSet χ {4, 5, 6, 7, 9} ↔
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0880
    (χ : TripleColoring 10) :
    IsCupSet χ {4, 5, 6, 8, 9} ↔
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0944
    (χ : TripleColoring 10) :
    IsCupSet χ {4, 5, 7, 8, 9} ↔
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_cupSet_iff_mask0976
    (χ : TripleColoring 10) :
    IsCupSet χ {4, 6, 7, 8, 9} ↔
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.left ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0109
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 3, 5, 6} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0173
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 3, 5, 7} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0301
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 3, 5, 8} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0557
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 3, 5, 9} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0205
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 3, 6, 7} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0333
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 3, 6, 8} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0589
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 3, 6, 9} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0397
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 3, 7, 8} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0653
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 3, 7, 9} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0781
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 3, 8, 9} ↔
      χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0229
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 5, 6, 7} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0357
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 5, 6, 8} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0613
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 5, 6, 9} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0421
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 5, 7, 8} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0677
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 5, 7, 9} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0805
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 5, 8, 9} ↔
      χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0453
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 6, 7, 8} ↔
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0709
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 6, 7, 9} ↔
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0837
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 6, 8, 9} ↔
      χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0901
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 2, 7, 8, 9} ↔
      χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 2, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0233
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 3, 5, 6, 7} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0361
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 3, 5, 6, 8} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0617
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 3, 5, 6, 9} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0425
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 3, 5, 7, 8} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0681
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 3, 5, 7, 9} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0809
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 3, 5, 8, 9} ↔
      χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0457
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 3, 6, 7, 8} ↔
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0713
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 3, 6, 7, 9} ↔
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0841
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 3, 6, 8, 9} ↔
      χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0905
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 3, 7, 8, 9} ↔
      χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0481
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 5, 6, 7, 8} ↔
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0737
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 5, 6, 7, 9} ↔
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0865
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 5, 6, 8, 9} ↔
      χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0929
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 5, 7, 8, 9} ↔
      χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0961
    (χ : TripleColoring 10) :
    IsCapSet χ {0, 6, 7, 8, 9} ↔
      χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨0, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0124
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 4, 5, 6} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0316
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 4, 5, 8} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0220
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 4, 6, 7} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0348
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 4, 6, 8} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0412
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 4, 7, 8} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0668
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 4, 7, 9} ↔
      χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0236
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 5, 6, 7} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0364
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 5, 6, 8} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0620
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 5, 6, 9} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0428
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 5, 7, 8} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0684
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 5, 7, 9} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0812
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 5, 8, 9} ↔
      χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0460
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 6, 7, 8} ↔
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0716
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 6, 7, 9} ↔
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0844
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 6, 8, 9} ↔
      χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0908
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 3, 7, 8, 9} ↔
      χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 3, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0244
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 4, 5, 6, 7} ↔
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0436
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 4, 5, 7, 8} ↔
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0692
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 4, 5, 7, 9} ↔
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0820
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 4, 5, 8, 9} ↔
      χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0468
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 4, 6, 7, 8} ↔
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0724
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 4, 6, 7, 9} ↔
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0852
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 4, 6, 8, 9} ↔
      χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0916
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 4, 7, 8, 9} ↔
      χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0484
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 5, 6, 7, 8} ↔
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0740
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 5, 6, 7, 9} ↔
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0868
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 5, 6, 8, 9} ↔
      χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0932
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 5, 7, 8, 9} ↔
      χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0964
    (χ : TripleColoring 10) :
    IsCapSet χ {2, 6, 7, 8, 9} ↔
      χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨2, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0248
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 4, 5, 6, 7} ↔
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0376
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 4, 5, 6, 8} ↔
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0632
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 4, 5, 6, 9} ↔
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0440
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 4, 5, 7, 8} ↔
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0696
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 4, 5, 7, 9} ↔
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0824
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 4, 5, 8, 9} ↔
      χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0472
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 4, 6, 7, 8} ↔
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0856
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 4, 6, 8, 9} ↔
      χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0920
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 4, 7, 8, 9} ↔
      χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 4, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0488
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 5, 6, 7, 8} ↔
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0744
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 5, 6, 7, 9} ↔
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0872
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 5, 6, 8, 9} ↔
      χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0936
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 5, 7, 8, 9} ↔
      χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0968
    (χ : TripleColoring 10) :
    IsCapSet χ {3, 6, 7, 8, 9} ↔
      χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨3, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0496
    (χ : TripleColoring 10) :
    IsCapSet χ {4, 5, 6, 7, 8} ↔
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0880
    (χ : TripleColoring 10) :
    IsCapSet χ {4, 5, 6, 8, 9} ↔
      χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0944
    (χ : TripleColoring 10) :
    IsCapSet χ {4, 5, 7, 8, 9} ↔
      χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 5, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0976
    (χ : TripleColoring 10) :
    IsCapSet χ {4, 6, 7, 8, 9} ↔
      χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨4, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_capSet_iff_mask0992
    (χ : TripleColoring 10) :
    IsCapSet χ {5, 6, 7, 8, 9} ↔
      χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 6, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨5, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 8, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 7, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨6, 8, 9, by decide, by decide⟩ = Turn.right ∧
      χ ⟨7, 8, 9, by decide, by decide⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> try omega

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0109 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 3, 5, 6} →
      polygon.card = 5 → polygon = {0, 2, 3, 5, 6} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0173 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 3, 5, 7} →
      polygon.card = 5 → polygon = {0, 2, 3, 5, 7} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0301 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 3, 5, 8} →
      polygon.card = 5 → polygon = {0, 2, 3, 5, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0557 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 3, 5, 9} →
      polygon.card = 5 → polygon = {0, 2, 3, 5, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0205 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 3, 6, 7} →
      polygon.card = 5 → polygon = {0, 2, 3, 6, 7} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0333 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 3, 6, 8} →
      polygon.card = 5 → polygon = {0, 2, 3, 6, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0589 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 3, 6, 9} →
      polygon.card = 5 → polygon = {0, 2, 3, 6, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0397 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 3, 7, 8} →
      polygon.card = 5 → polygon = {0, 2, 3, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0653 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 3, 7, 9} →
      polygon.card = 5 → polygon = {0, 2, 3, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0781 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 3, 8, 9} →
      polygon.card = 5 → polygon = {0, 2, 3, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0229 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 5, 6, 7} →
      polygon.card = 5 → polygon = {0, 2, 5, 6, 7} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0357 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 5, 6, 8} →
      polygon.card = 5 → polygon = {0, 2, 5, 6, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0613 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 5, 6, 9} →
      polygon.card = 5 → polygon = {0, 2, 5, 6, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0421 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 5, 7, 8} →
      polygon.card = 5 → polygon = {0, 2, 5, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0677 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 5, 7, 9} →
      polygon.card = 5 → polygon = {0, 2, 5, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0805 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 5, 8, 9} →
      polygon.card = 5 → polygon = {0, 2, 5, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0453 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 6, 7, 8} →
      polygon.card = 5 → polygon = {0, 2, 6, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0709 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 6, 7, 9} →
      polygon.card = 5 → polygon = {0, 2, 6, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0837 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 6, 8, 9} →
      polygon.card = 5 → polygon = {0, 2, 6, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0901 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 2, 7, 8, 9} →
      polygon.card = 5 → polygon = {0, 2, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0233 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 3, 5, 6, 7} →
      polygon.card = 5 → polygon = {0, 3, 5, 6, 7} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0361 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 3, 5, 6, 8} →
      polygon.card = 5 → polygon = {0, 3, 5, 6, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0617 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 3, 5, 6, 9} →
      polygon.card = 5 → polygon = {0, 3, 5, 6, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0425 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 3, 5, 7, 8} →
      polygon.card = 5 → polygon = {0, 3, 5, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0681 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 3, 5, 7, 9} →
      polygon.card = 5 → polygon = {0, 3, 5, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0809 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 3, 5, 8, 9} →
      polygon.card = 5 → polygon = {0, 3, 5, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0457 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 3, 6, 7, 8} →
      polygon.card = 5 → polygon = {0, 3, 6, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0713 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 3, 6, 7, 9} →
      polygon.card = 5 → polygon = {0, 3, 6, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0841 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 3, 6, 8, 9} →
      polygon.card = 5 → polygon = {0, 3, 6, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0905 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 3, 7, 8, 9} →
      polygon.card = 5 → polygon = {0, 3, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0481 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 5, 6, 7, 8} →
      polygon.card = 5 → polygon = {0, 5, 6, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0737 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 5, 6, 7, 9} →
      polygon.card = 5 → polygon = {0, 5, 6, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0865 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 5, 6, 8, 9} →
      polygon.card = 5 → polygon = {0, 5, 6, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0929 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 5, 7, 8, 9} →
      polygon.card = 5 → polygon = {0, 5, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0961 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {0, 6, 7, 8, 9} →
      polygon.card = 5 → polygon = {0, 6, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0124 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 4, 5, 6} →
      polygon.card = 5 → polygon = {2, 3, 4, 5, 6} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0316 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 4, 5, 8} →
      polygon.card = 5 → polygon = {2, 3, 4, 5, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0572 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 4, 5, 9} →
      polygon.card = 5 → polygon = {2, 3, 4, 5, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0220 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 4, 6, 7} →
      polygon.card = 5 → polygon = {2, 3, 4, 6, 7} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0348 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 4, 6, 8} →
      polygon.card = 5 → polygon = {2, 3, 4, 6, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0604 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 4, 6, 9} →
      polygon.card = 5 → polygon = {2, 3, 4, 6, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0412 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 4, 7, 8} →
      polygon.card = 5 → polygon = {2, 3, 4, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0668 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 4, 7, 9} →
      polygon.card = 5 → polygon = {2, 3, 4, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0796 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 4, 8, 9} →
      polygon.card = 5 → polygon = {2, 3, 4, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0236 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 5, 6, 7} →
      polygon.card = 5 → polygon = {2, 3, 5, 6, 7} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0364 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 5, 6, 8} →
      polygon.card = 5 → polygon = {2, 3, 5, 6, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0620 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 5, 6, 9} →
      polygon.card = 5 → polygon = {2, 3, 5, 6, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0428 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 5, 7, 8} →
      polygon.card = 5 → polygon = {2, 3, 5, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0684 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 5, 7, 9} →
      polygon.card = 5 → polygon = {2, 3, 5, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0812 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 5, 8, 9} →
      polygon.card = 5 → polygon = {2, 3, 5, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0460 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 6, 7, 8} →
      polygon.card = 5 → polygon = {2, 3, 6, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0716 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 6, 7, 9} →
      polygon.card = 5 → polygon = {2, 3, 6, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0844 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 6, 8, 9} →
      polygon.card = 5 → polygon = {2, 3, 6, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0908 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 3, 7, 8, 9} →
      polygon.card = 5 → polygon = {2, 3, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0244 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 4, 5, 6, 7} →
      polygon.card = 5 → polygon = {2, 4, 5, 6, 7} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0372 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 4, 5, 6, 8} →
      polygon.card = 5 → polygon = {2, 4, 5, 6, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0628 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 4, 5, 6, 9} →
      polygon.card = 5 → polygon = {2, 4, 5, 6, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0436 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 4, 5, 7, 8} →
      polygon.card = 5 → polygon = {2, 4, 5, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0692 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 4, 5, 7, 9} →
      polygon.card = 5 → polygon = {2, 4, 5, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0820 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 4, 5, 8, 9} →
      polygon.card = 5 → polygon = {2, 4, 5, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0468 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 4, 6, 7, 8} →
      polygon.card = 5 → polygon = {2, 4, 6, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0724 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 4, 6, 7, 9} →
      polygon.card = 5 → polygon = {2, 4, 6, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0852 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 4, 6, 8, 9} →
      polygon.card = 5 → polygon = {2, 4, 6, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0916 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 4, 7, 8, 9} →
      polygon.card = 5 → polygon = {2, 4, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0484 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 5, 6, 7, 8} →
      polygon.card = 5 → polygon = {2, 5, 6, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0740 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 5, 6, 7, 9} →
      polygon.card = 5 → polygon = {2, 5, 6, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0868 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 5, 6, 8, 9} →
      polygon.card = 5 → polygon = {2, 5, 6, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0932 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 5, 7, 8, 9} →
      polygon.card = 5 → polygon = {2, 5, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0964 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {2, 6, 7, 8, 9} →
      polygon.card = 5 → polygon = {2, 6, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0248 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 4, 5, 6, 7} →
      polygon.card = 5 → polygon = {3, 4, 5, 6, 7} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0376 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 4, 5, 6, 8} →
      polygon.card = 5 → polygon = {3, 4, 5, 6, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0632 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 4, 5, 6, 9} →
      polygon.card = 5 → polygon = {3, 4, 5, 6, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0440 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 4, 5, 7, 8} →
      polygon.card = 5 → polygon = {3, 4, 5, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0696 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 4, 5, 7, 9} →
      polygon.card = 5 → polygon = {3, 4, 5, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0824 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 4, 5, 8, 9} →
      polygon.card = 5 → polygon = {3, 4, 5, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0472 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 4, 6, 7, 8} →
      polygon.card = 5 → polygon = {3, 4, 6, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0856 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 4, 6, 8, 9} →
      polygon.card = 5 → polygon = {3, 4, 6, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0920 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 4, 7, 8, 9} →
      polygon.card = 5 → polygon = {3, 4, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0488 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 5, 6, 7, 8} →
      polygon.card = 5 → polygon = {3, 5, 6, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0744 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 5, 6, 7, 9} →
      polygon.card = 5 → polygon = {3, 5, 6, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0872 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 5, 6, 8, 9} →
      polygon.card = 5 → polygon = {3, 5, 6, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0936 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 5, 7, 8, 9} →
      polygon.card = 5 → polygon = {3, 5, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0968 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {3, 6, 7, 8, 9} →
      polygon.card = 5 → polygon = {3, 6, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0496 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {4, 5, 6, 7, 8} →
      polygon.card = 5 → polygon = {4, 5, 6, 7, 8} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0752 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {4, 5, 6, 7, 9} →
      polygon.card = 5 → polygon = {4, 5, 6, 7, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0880 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {4, 5, 6, 8, 9} →
      polygon.card = 5 → polygon = {4, 5, 6, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0944 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {4, 5, 7, 8, 9} →
      polygon.card = 5 → polygon = {4, 5, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0976 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {4, 6, 7, 8, 9} →
      polygon.card = 5 → polygon = {4, 6, 7, 8, 9} := by decide

theorem halfPureSingletonFanFin10_fiveSubset_eq_mask0992 :
    ∀ polygon : Finset (Fin 10), polygon ⊆ {5, 6, 7, 8, 9} →
      polygon.card = 5 → polygon = {5, 6, 7, 8, 9} := by decide

end ErdosSzekeres

end
