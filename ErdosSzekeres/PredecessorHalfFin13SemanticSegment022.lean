module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk016
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk017

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 022. -/

theorem predecessorHalfFin13_rejectSemanticSegment022
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi))) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0676 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0676 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0676 chi))) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0676 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0676 chi))))) ∨
      ((((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi))) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi)))) ∨
      (((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi))) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0677 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0677 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0677 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi))) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0677 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi))) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi))))) ∨
      ((((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0678 chi))) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0678 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0678 chi)))) ∨
      (((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0678 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi))) ∨
      (((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi)) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi))) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) ∨
      ((¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0679 chi) ∨
      (¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0679 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0679 chi) ∨
      (PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi))) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0679 chi) ∨
      ((PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) ∨
      (¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) ∨
      ((¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi) ∨
      (¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi))) ∨
      ((PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi) ∨
      ((PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi) ∨
      (PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi)))) ∨
      (((PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi) ∨
      ((¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) ∨
      (¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi))) ∨
      ((¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) ∨
      ((¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi) ∨
      (¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi) ∨
      ((PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi) ∨
      (PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi))) ∨
      ((PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0680 chi) ∨
      ((PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0139 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) ∨
      (¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi) ∨
      ((¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi) ∨
      (¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi))) ∨
      ((PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi) ∨
      ((PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi) ∨
      (PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi))))) ∨
      ((((PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi) ∨
      ((¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) ∨
      (¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0681 chi))) ∨
      ((¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0681 chi) ∨
      ((¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) ∨
      (¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0681 chi)))) ∨
      (((PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0681 chi) ∨
      ((PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) ∨
      (PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0681 chi))) ∨
      (((PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0140 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) ∨
      (¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi)) ∨
      ((¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi) ∨
      (¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0141 chi ∧
      PredecessorHalfFin13Atom0177 chi))))))))) := by
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
              exact predecessorHalfFin13_clause09341 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09342 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09343 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09344 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09345 chi hbad
              ·
                exact predecessorHalfFin13_clause09346 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09348 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09352 chi hbad
              ·
                exact predecessorHalfFin13_clause09353 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09354 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09357 chi hbad
              ·
                exact predecessorHalfFin13_clause09359 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09360 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09361 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09362 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09363 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09364 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09365 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09366 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09367 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09368 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09369 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09370 chi hbad
              ·
                exact predecessorHalfFin13_clause09372 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09376 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09377 chi hbad
              ·
                exact predecessorHalfFin13_clause09381 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09383 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09384 chi hbad
              ·
                exact predecessorHalfFin13_clause09385 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09386 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09387 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09388 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09389 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09390 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09391 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09392 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09393 chi hbad
              ·
                exact predecessorHalfFin13_clause09394 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09396 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09400 chi hbad
              ·
                exact predecessorHalfFin13_clause09401 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09407 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09408 chi hbad
              ·
                exact predecessorHalfFin13_clause09409 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09410 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09411 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09412 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09413 chi hone hbad
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
              exact predecessorHalfFin13_clause09414 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09415 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09416 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09417 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09418 chi hbad
              ·
                exact predecessorHalfFin13_clause09420 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09424 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09425 chi hbad
              ·
                exact predecessorHalfFin13_clause09429 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09431 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09432 chi hbad
              ·
                exact predecessorHalfFin13_clause09433 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09434 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09435 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09436 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09437 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09438 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09439 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09440 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09441 chi hbad
              ·
                exact predecessorHalfFin13_clause09442 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09444 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09445 chi hbad
              ·
                exact predecessorHalfFin13_clause09446 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09448 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09449 chi hbad
              ·
                exact predecessorHalfFin13_clause09453 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09455 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09456 chi hbad
              ·
                exact predecessorHalfFin13_clause09457 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09458 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09459 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09460 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09461 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09462 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09463 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09464 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09465 chi hbad
              ·
                exact predecessorHalfFin13_clause09466 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09467 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09468 chi hbad
              ·
                exact predecessorHalfFin13_clause09472 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause09473 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09477 chi hbad
              ·
                exact predecessorHalfFin13_clause09479 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09480 chi hbad
              ·
                exact predecessorHalfFin13_clause09481 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause09482 chi hone hbad
              ·
                exact predecessorHalfFin13_clause09483 chi hone hbad

end ErdosSzekeres

end
