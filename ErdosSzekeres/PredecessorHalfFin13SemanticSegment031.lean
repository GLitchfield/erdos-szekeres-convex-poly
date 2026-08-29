module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk023
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk024

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 031. -/

theorem predecessorHalfFin13_rejectSemanticSegment031
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi))) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi)))) ∨
      (((PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi) ∨
      (PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi))) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0728 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0728 chi) ∨
      (PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0728 chi))) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0728 chi) ∨
      (PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi))) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi) ∨
      (PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi))) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0729 chi) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0729 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0729 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0729 chi) ∨
      (PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi))) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0729 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) ∨
      ((¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi))) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) ∨
      (PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi)))) ∨
      (((PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi) ∨
      ((¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi))) ∨
      (((¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi)) ∨
      ((¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) ∨
      (PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi))) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0730 chi) ∨
      (PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi) ∨
      ((¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi))) ∨
      ((¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi) ∨
      (PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi))))) ∨
      ((((PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi))) ∨
      ((¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0731 chi) ∨
      ((¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0731 chi)))) ∨
      (((PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0731 chi) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) ∨
      (PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0731 chi))) ∨
      (((PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi)) ∨
      ((¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi) ∨
      (PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi))) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0732 chi) ∨
      ((¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) ∨
      (¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0732 chi))) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0732 chi) ∨
      ((PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) ∨
      (PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0732 chi))))) ∨
      ((((PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) ∨
      ((¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi) ∨
      (¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi))) ∨
      ((¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi) ∨
      ((¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi) ∨
      (PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi)))) ∨
      (((PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi) ∨
      ((PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi) ∨
      (PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi))) ∨
      (((¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) ∨
      (¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0733 chi)) ∨
      ((¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0733 chi) ∨
      (¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi))))))))) := by
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
              exact predecessorHalfFin13_clause10583 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10584 chi hbad
              ·
                exact predecessorHalfFin13_clause10585 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10586 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10587 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10588 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10589 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10590 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10591 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10592 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10593 chi hbad
              ·
                exact predecessorHalfFin13_clause10594 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10596 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10600 chi hbad
              ·
                exact predecessorHalfFin13_clause10601 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10605 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10607 chi hbad
              ·
                exact predecessorHalfFin13_clause10608 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10609 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10610 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10611 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10612 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10613 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10614 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10615 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10616 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10617 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10618 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10619 chi hbad
              ·
                exact predecessorHalfFin13_clause10620 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10624 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10625 chi hbad
              ·
                exact predecessorHalfFin13_clause10629 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10631 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10632 chi hbad
              ·
                exact predecessorHalfFin13_clause10633 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10634 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10635 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10636 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10637 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10638 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10639 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10640 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10641 chi hbad
              ·
                exact predecessorHalfFin13_clause10642 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10643 chi hbad
              ·
                exact predecessorHalfFin13_clause10644 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10646 chi hbad
              ·
                exact predecessorHalfFin13_clause10647 chi hbad
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
              exact predecessorHalfFin13_clause10648 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10649 chi hbad
              ·
                exact predecessorHalfFin13_clause10652 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10653 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10655 chi hbad
              ·
                exact predecessorHalfFin13_clause10656 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10657 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10658 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10659 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10660 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10661 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10662 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10663 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10664 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10665 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10666 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10668 chi hbad
              ·
                exact predecessorHalfFin13_clause10672 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10673 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10677 chi hbad
              ·
                exact predecessorHalfFin13_clause10679 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10680 chi hbad
              ·
                exact predecessorHalfFin13_clause10681 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10682 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10683 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10684 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10685 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10686 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10687 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10688 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10689 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10690 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10692 chi hbad
              ·
                exact predecessorHalfFin13_clause10696 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10697 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10701 chi hbad
              ·
                exact predecessorHalfFin13_clause10703 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10704 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10705 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10706 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10707 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10708 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10709 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10710 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10711 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10712 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10713 chi hbad
              ·
                exact predecessorHalfFin13_clause10714 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10715 chi hbad
              ·
                exact predecessorHalfFin13_clause10716 chi hbad

end ErdosSzekeres

end
