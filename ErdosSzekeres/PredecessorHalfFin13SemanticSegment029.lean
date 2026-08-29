module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk022
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk023

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 029. -/

theorem predecessorHalfFin13_rejectSemanticSegment029
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0716 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0716 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0716 chi))) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0716 chi) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0716 chi)))) ∨
      (((PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) ∨
      (¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi))) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi))))) ∨
      ((((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi))) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0717 chi) ∨
      (¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0717 chi) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0717 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi))) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0717 chi) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) ∨
      (¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi) ∨
      (¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi))) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi)))) ∨
      (((PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) ∨
      (¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0718 chi))) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0718 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0718 chi))))) ∨
      ((((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0718 chi) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0718 chi))) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) ∨
      (¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi))) ∨
      (((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi)) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi) ∨
      (¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0719 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) ∨
      (¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0719 chi))) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0719 chi) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0719 chi)))) ∨
      (((PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) ∨
      (¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi))) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi))))) ∨
      ((((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi))) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) ∨
      ((¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi) ∨
      (¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi))) ∨
      (((PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi)) ∨
      ((PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi) ∨
      (PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi))) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi)))) ∨
      (((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi))) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi))) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi))) ∨
      (((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi)) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi))))))))) := by
  intro hbad
  rcases hbad with hbad | hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10310 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10312 chi hbad
              ·
                exact predecessorHalfFin13_clause10313 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10315 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10317 chi hbad
              ·
                exact predecessorHalfFin13_clause10319 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10320 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10321 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10322 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10323 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10324 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10325 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10326 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10327 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10328 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10329 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10330 chi hbad
              ·
                exact predecessorHalfFin13_clause10332 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10336 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10337 chi hbad
              ·
                exact predecessorHalfFin13_clause10341 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10343 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10344 chi hbad
              ·
                exact predecessorHalfFin13_clause10345 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10346 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10347 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10348 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10349 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10350 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10351 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10352 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10353 chi hbad
              ·
                exact predecessorHalfFin13_clause10354 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10356 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10360 chi hbad
              ·
                exact predecessorHalfFin13_clause10361 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10363 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10365 chi hbad
              ·
                exact predecessorHalfFin13_clause10367 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10368 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10369 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10370 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10371 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10372 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10373 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10374 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10375 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10376 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10377 chi hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10378 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10380 chi hbad
              ·
                exact predecessorHalfFin13_clause10384 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10385 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10389 chi hbad
              ·
                exact predecessorHalfFin13_clause10391 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10392 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10393 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10394 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10395 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10396 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10397 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10398 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10399 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10400 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10401 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10402 chi hbad
              ·
                exact predecessorHalfFin13_clause10404 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10408 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10409 chi hbad
              ·
                exact predecessorHalfFin13_clause10411 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10412 chi hbad
              ·
                exact predecessorHalfFin13_clause10413 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10415 chi hbad
              ·
                exact predecessorHalfFin13_clause10416 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10417 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10418 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10419 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10420 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10421 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10422 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10423 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10424 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10425 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10426 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10427 chi hbad
              ·
                exact predecessorHalfFin13_clause10428 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10432 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10433 chi hbad
              ·
                exact predecessorHalfFin13_clause10436 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10437 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10439 chi hbad
              ·
                exact predecessorHalfFin13_clause10440 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10441 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10442 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10443 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10444 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10445 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10446 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10447 chi hone hbad

end ErdosSzekeres

end
