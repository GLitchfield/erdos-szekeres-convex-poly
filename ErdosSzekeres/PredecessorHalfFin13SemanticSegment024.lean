module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk018
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk019

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 024. -/

theorem predecessorHalfFin13_rejectSemanticSegment024
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0687 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi))) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi))) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi))) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi)))) ∨
      (((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0688 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi))) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi))) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0689 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0689 chi))) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0689 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0689 chi))))) ∨
      ((((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi))) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi)))) ∨
      (((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi))) ∨
      (((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi)) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi))) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0690 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi))) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi))))) ∨
      ((((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi))) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0691 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0691 chi)))) ∨
      (((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0691 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0691 chi))) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0691 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi))) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) ∨
      (¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi))) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) ∨
      ((¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi))))) ∨
      ((((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) ∨
      (PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi))) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0692 chi) ∨
      ((PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) ∨
      (¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi) ∨
      ((¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi) ∨
      (¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi))) ∨
      (((PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi) ∨
      (PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi)) ∨
      ((PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi) ∨
      (PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0188 chi))))))))) := by
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
              exact predecessorHalfFin13_clause09621 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09623 chi hbad
              ·
                exact predecessorHalfFin13_clause09624 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09625 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09626 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09627 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09628 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09629 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09630 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09631 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09632 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09633 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09634 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09636 chi hbad
              ·
                exact predecessorHalfFin13_clause09640 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09641 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09642 chi hbad
              ·
                exact predecessorHalfFin13_clause09645 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09646 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09647 chi hbad
              ·
                exact predecessorHalfFin13_clause09648 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09649 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09650 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09651 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09652 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09653 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09654 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09655 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09656 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09657 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09658 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09660 chi hbad
              ·
                exact predecessorHalfFin13_clause09664 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09665 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09669 chi hbad
              ·
                exact predecessorHalfFin13_clause09671 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09672 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09673 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09674 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09675 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09676 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09677 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09678 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09679 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09680 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09681 chi hbad
              ·
                exact predecessorHalfFin13_clause09682 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09683 chi hbad
              ·
                exact predecessorHalfFin13_clause09684 chi hbad
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
              exact predecessorHalfFin13_clause09688 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09689 chi hbad
              ·
                exact predecessorHalfFin13_clause09692 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09693 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09695 chi hbad
              ·
                exact predecessorHalfFin13_clause09696 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09697 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09698 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09699 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09700 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09701 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09702 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09703 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09704 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09705 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09706 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09708 chi hbad
              ·
                exact predecessorHalfFin13_clause09712 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09713 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09717 chi hbad
              ·
                exact predecessorHalfFin13_clause09719 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09720 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09721 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09722 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09723 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09724 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09725 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09726 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09727 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09728 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09729 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09730 chi hbad
              ·
                exact predecessorHalfFin13_clause09731 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09732 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09736 chi hbad
              ·
                exact predecessorHalfFin13_clause09737 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09739 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09740 chi hbad
              ·
                exact predecessorHalfFin13_clause09741 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09743 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09744 chi hbad
              ·
                exact predecessorHalfFin13_clause09745 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09746 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09747 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09748 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09749 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09750 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09751 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09752 chi hone hbad

end ErdosSzekeres

end
