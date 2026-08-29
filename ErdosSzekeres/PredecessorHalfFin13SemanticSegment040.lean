module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk030
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk031

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 040. -/

theorem predecessorHalfFin13_rejectSemanticSegment040
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0778 chi) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) ∨
      (PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0778 chi))) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) ∨
      ((¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) ∨
      (¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0274 chi) ∨
      ((¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) ∨
      (PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0274 chi))) ∨
      ((PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) ∨
      ((PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0274 chi) ∨
      (PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0274 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) ∨
      ((¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0779 chi) ∨
      (¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0779 chi))) ∨
      ((¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) ∨
      ((¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0779 chi) ∨
      (¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0779 chi)))) ∨
      (((PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0779 chi) ∨
      ((PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) ∨
      (PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0779 chi))) ∨
      ((PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) ∨
      ((¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) ∨
      (¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0275 chi) ∨
      ((¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) ∨
      (PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0275 chi))) ∨
      ((PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) ∨
      ((PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0275 chi) ∨
      (PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0275 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) ∨
      ((¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0780 chi) ∨
      (¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0780 chi))) ∨
      ((¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) ∨
      ((¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0780 chi) ∨
      (¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0780 chi))))) ∨
      ((((PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0780 chi) ∨
      ((PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) ∨
      (PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0780 chi))) ∨
      ((PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) ∨
      ((¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) ∨
      (¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi) ∨
      ((¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) ∨
      (PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi))) ∨
      (((PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi) ∨
      (PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi)) ∨
      ((¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) ∨
      (¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0781 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) ∨
      ((¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0781 chi) ∨
      (PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi))) ∨
      ((PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0781 chi) ∨
      ((PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) ∨
      (¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) ∨
      ((¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      (¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi))) ∨
      ((PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      ((PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) ∨
      (PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi))))) ∨
      ((((PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      ((¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) ∨
      (¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0782 chi))) ∨
      ((¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) ∨
      ((¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0782 chi) ∨
      (¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0782 chi)))) ∨
      (((PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0782 chi) ∨
      ((PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) ∨
      (PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0782 chi))) ∨
      ((PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) ∨
      ((¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) ∨
      (¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi) ∨
      ((¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) ∨
      (PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi))) ∨
      ((PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) ∨
      ((PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi) ∨
      (PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) ∨
      ((¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0783 chi) ∨
      (¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi))) ∨
      ((¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0783 chi) ∨
      ((PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0783 chi) ∨
      (PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi))))) ∨
      ((((PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0783 chi) ∨
      ((PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) ∨
      (¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi))) ∨
      ((¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) ∨
      ((¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi) ∨
      (¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi)))) ∨
      (((PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi) ∨
      ((PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) ∨
      (PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi))) ∨
      (((PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi) ∨
      (¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi)) ∨
      ((¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0784 chi) ∨
      (¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi))))))))) := by
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
              exact predecessorHalfFin13_clause11804 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11805 chi hbad
              ·
                exact predecessorHalfFin13_clause11807 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11808 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11809 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11810 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11811 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11812 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11813 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11814 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11815 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11816 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11817 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11818 chi hbad
              ·
                exact predecessorHalfFin13_clause11819 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11820 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11822 chi hbad
              ·
                exact predecessorHalfFin13_clause11824 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11825 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11829 chi hbad
              ·
                exact predecessorHalfFin13_clause11831 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11832 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11833 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11834 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11835 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11836 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11837 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11838 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11839 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11840 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11841 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11842 chi hbad
              ·
                exact predecessorHalfFin13_clause11843 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11844 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11846 chi hbad
              ·
                exact predecessorHalfFin13_clause11848 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11849 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11853 chi hbad
              ·
                exact predecessorHalfFin13_clause11855 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11856 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11857 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11858 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11859 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11860 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11862 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11863 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11864 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11865 chi hbad
              ·
                exact predecessorHalfFin13_clause11867 chi hbad
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
              exact predecessorHalfFin13_clause11868 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11872 chi hbad
              ·
                exact predecessorHalfFin13_clause11877 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11879 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11880 chi hbad
              ·
                exact predecessorHalfFin13_clause11881 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11882 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11883 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11884 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11885 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11886 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11887 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11888 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11889 chi hbad
              ·
                exact predecessorHalfFin13_clause11890 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11892 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11894 chi hbad
              ·
                exact predecessorHalfFin13_clause11896 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11897 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11901 chi hbad
              ·
                exact predecessorHalfFin13_clause11903 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11904 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11905 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11906 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11907 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11908 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11909 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11910 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11911 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11912 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11913 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11914 chi hbad
              ·
                exact predecessorHalfFin13_clause11916 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11920 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11921 chi hbad
              ·
                exact predecessorHalfFin13_clause11925 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11927 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11928 chi hbad
              ·
                exact predecessorHalfFin13_clause11929 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11930 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11931 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11932 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11933 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11934 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11935 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11936 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11937 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11938 chi hbad
              ·
                exact predecessorHalfFin13_clause11940 chi hbad

end ErdosSzekeres

end
