module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk032
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk033

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 042. -/

theorem predecessorHalfFin13_rejectSemanticSegment042
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) ∨
      ((PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi) ∨
      (PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi))) ∨
      ((¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) ∨
      ((¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0790 chi) ∨
      (¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0790 chi) ∨
      ((PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0790 chi) ∨
      (PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0790 chi))) ∨
      ((PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) ∨
      ((PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0790 chi) ∨
      (PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      ((¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      (¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi))) ∨
      ((¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      ((PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      (PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi)))) ∨
      (((PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      ((PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      (¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi))) ∨
      ((¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0791 chi) ∨
      ((¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0791 chi) ∨
      (PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0791 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) ∨
      ((PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0791 chi) ∨
      (PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi))) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi) ∨
      (PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi))) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0792 chi) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0792 chi))) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0792 chi) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0792 chi) ∨
      (PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi)))) ∨
      (((PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0792 chi) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi))) ∨
      (((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi)) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi) ∨
      (PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi) ∨
      (PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi))) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi))) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) ∨
      (PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi))))) ∨
      ((((PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi))) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi)))) ∨
      (((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi) ∨
      (PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi))) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0794 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0794 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0794 chi))) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0794 chi) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      (PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0794 chi)))) ∨
      (((PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi))) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) ∨
      (PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi))))) ∨
      ((((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi) ∨
      (PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi))) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0795 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0795 chi) ∨
      ((PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0795 chi) ∨
      (PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi))) ∨
      (((PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0795 chi) ∨
      (PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi)) ∨
      ((¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi) ∨
      (¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi))))))))) := by
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
              exact predecessorHalfFin13_clause12078 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12079 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12080 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12081 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12082 chi hbad
              ·
                exact predecessorHalfFin13_clause12084 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12088 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12089 chi hbad
              ·
                exact predecessorHalfFin13_clause12091 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12093 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12095 chi hbad
              ·
                exact predecessorHalfFin13_clause12096 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12097 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12098 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12099 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12100 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12101 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12102 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12103 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12104 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12105 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12106 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12112 chi hbad
              ·
                exact predecessorHalfFin13_clause12113 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12117 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12119 chi hbad
              ·
                exact predecessorHalfFin13_clause12120 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12121 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12122 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12123 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12124 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12125 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12126 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12127 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12128 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12129 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12130 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12132 chi hbad
              ·
                exact predecessorHalfFin13_clause12135 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12136 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12137 chi hbad
              ·
                exact predecessorHalfFin13_clause12141 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12143 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12144 chi hbad
              ·
                exact predecessorHalfFin13_clause12145 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12146 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12147 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12148 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12149 chi hone hbad
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
              exact predecessorHalfFin13_clause12150 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12151 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12152 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12153 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12154 chi hbad
              ·
                exact predecessorHalfFin13_clause12156 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12158 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12159 chi hbad
              ·
                exact predecessorHalfFin13_clause12160 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12161 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12163 chi hbad
              ·
                exact predecessorHalfFin13_clause12165 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12167 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12168 chi hbad
              ·
                exact predecessorHalfFin13_clause12169 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12170 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12171 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12172 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12173 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12174 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12175 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12176 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12177 chi hbad
              ·
                exact predecessorHalfFin13_clause12178 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12180 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12182 chi hbad
              ·
                exact predecessorHalfFin13_clause12184 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12185 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12189 chi hbad
              ·
                exact predecessorHalfFin13_clause12191 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12192 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12193 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12194 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12195 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12196 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12197 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12198 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12199 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12200 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12201 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12202 chi hbad
              ·
                exact predecessorHalfFin13_clause12204 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12208 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12209 chi hbad
              ·
                exact predecessorHalfFin13_clause12213 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12215 chi hbad
              ·
                exact predecessorHalfFin13_clause12216 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12217 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12218 chi hone hbad

end ErdosSzekeres

end
