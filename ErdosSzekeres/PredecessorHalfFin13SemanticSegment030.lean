module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk023

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 030. -/

theorem predecessorHalfFin13_rejectSemanticSegment030
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi))) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi)))) ∨
      (((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi))) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0722 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi))) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi)))) ∨
      (((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi))) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi))) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0723 chi)))) ∨
      (((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi))) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi))))) ∨
      ((((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi))) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0724 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0724 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0724 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi))) ∨
      (((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0724 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi)) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi))) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0725 chi) ∨
      (¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi))) ∨
      ((¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0725 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0725 chi) ∨
      (PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi))))) ∨
      ((((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0725 chi) ∨
      ((PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi))) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi)))) ∨
      (((PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi) ∨
      (PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi))) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi))) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi) ∨
      (PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi)))) ∨
      (((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0726 chi) ∨
      (PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi))) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi) ∨
      (PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi))) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi) ∨
      ((¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) ∨
      (¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi))) ∨
      (((PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi) ∨
      (PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi)) ∨
      ((PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) ∨
      (PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0727 chi))))))))) := by
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
              exact predecessorHalfFin13_clause10448 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10449 chi hbad
              ·
                exact predecessorHalfFin13_clause10450 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10452 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10455 chi hbad
              ·
                exact predecessorHalfFin13_clause10456 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10457 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10460 chi hbad
              ·
                exact predecessorHalfFin13_clause10461 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10463 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10464 chi hbad
              ·
                exact predecessorHalfFin13_clause10465 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10466 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10467 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10468 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10469 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10470 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10471 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10472 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10473 chi hbad
              ·
                exact predecessorHalfFin13_clause10474 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10475 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10476 chi hbad
              ·
                exact predecessorHalfFin13_clause10478 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10480 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10481 chi hbad
              ·
                exact predecessorHalfFin13_clause10482 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10485 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10486 chi hbad
              ·
                exact predecessorHalfFin13_clause10487 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10488 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10489 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10490 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10491 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10492 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10493 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10494 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10495 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10496 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10497 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10498 chi hbad
              ·
                exact predecessorHalfFin13_clause10500 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10504 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10505 chi hbad
              ·
                exact predecessorHalfFin13_clause10509 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10511 chi hbad
              ·
                exact predecessorHalfFin13_clause10512 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10513 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10514 chi hone hbad
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
              exact predecessorHalfFin13_clause10515 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10516 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10517 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10518 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10519 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10520 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10521 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10522 chi hbad
              ·
                exact predecessorHalfFin13_clause10524 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10528 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10529 chi hbad
              ·
                exact predecessorHalfFin13_clause10533 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10535 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10536 chi hbad
              ·
                exact predecessorHalfFin13_clause10537 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10538 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10539 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10540 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10541 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10542 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10543 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10544 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10545 chi hbad
              ·
                exact predecessorHalfFin13_clause10546 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10547 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10548 chi hbad
              ·
                exact predecessorHalfFin13_clause10551 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10552 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10553 chi hbad
              ·
                exact predecessorHalfFin13_clause10556 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10557 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10559 chi hbad
              ·
                exact predecessorHalfFin13_clause10560 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10561 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10562 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10563 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10564 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10565 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10566 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10567 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10568 chi hone hbad
              ·
                exact predecessorHalfFin13_clause10569 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause10570 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10572 chi hbad
              ·
                exact predecessorHalfFin13_clause10576 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10577 chi hbad
              ·
                exact predecessorHalfFin13_clause10579 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause10581 chi hbad
              ·
                exact predecessorHalfFin13_clause10582 chi hbad

end ErdosSzekeres

end
