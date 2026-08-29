module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk035
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk036

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 046. -/

theorem predecessorHalfFin13_rejectSemanticSegment046
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0224 chi) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0224 chi))) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0224 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0224 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0813 chi) ∨
      (¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi))) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0813 chi) ∨
      ((¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0813 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0813 chi))))) ∨
      ((((PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0813 chi) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) ∨
      (PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0813 chi))) ∨
      ((PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) ∨
      ((¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) ∨
      (¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0225 chi) ∨
      ((¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) ∨
      (PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0225 chi))) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0225 chi) ∨
      (PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0225 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) ∨
      ((¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0814 chi) ∨
      (¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi))) ∨
      ((¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0814 chi) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0814 chi) ∨
      (PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0814 chi)))) ∨
      (((PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0814 chi) ∨
      (PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi))) ∨
      ((¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi) ∨
      ((¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi) ∨
      (¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0226 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0226 chi) ∨
      (PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi))) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0226 chi) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0226 chi) ∨
      (¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0815 chi) ∨
      ((¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) ∨
      (¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0815 chi))) ∨
      (((¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0815 chi) ∨
      (PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0815 chi)) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0815 chi) ∨
      (PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0815 chi) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) ∨
      (¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi))) ∨
      ((¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) ∨
      ((¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0227 chi) ∨
      (¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi)))) ∨
      (((PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0227 chi) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi) ∨
      (PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0227 chi))) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0227 chi) ∨
      ((¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) ∨
      (¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0816 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) ∨
      ((¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0816 chi) ∨
      (PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0816 chi))) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0816 chi) ∨
      ((PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) ∨
      (PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0816 chi)))) ∨
      (((PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) ∨
      ((¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi) ∨
      (¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi))) ∨
      ((¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0228 chi) ∨
      ((¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi) ∨
      (PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0228 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi) ∨
      ((PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0228 chi) ∨
      (PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0228 chi))) ∨
      ((¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) ∨
      ((¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0817 chi) ∨
      (¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0817 chi) ∨
      ((PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0817 chi) ∨
      (PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi))) ∨
      ((PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0817 chi) ∨
      ((PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0817 chi) ∨
      (PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi) ∨
      ((¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi) ∨
      (¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0229 chi))) ∨
      ((¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi) ∨
      ((PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0229 chi) ∨
      (PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi)))) ∨
      (((PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0229 chi) ∨
      ((PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0229 chi) ∨
      (¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi))) ∨
      (((¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0818 chi) ∨
      (¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi)) ∨
      ((¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0818 chi) ∨
      (¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0818 chi))))))))) := by
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
              exact predecessorHalfFin13_clause12627 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12628 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12629 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12630 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12631 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12632 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12633 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12634 chi hbad
              ·
                exact predecessorHalfFin13_clause12636 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12639 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12640 chi hbad
              ·
                exact predecessorHalfFin13_clause12641 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12642 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12645 chi hbad
              ·
                exact predecessorHalfFin13_clause12647 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12648 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12649 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12650 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12651 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12652 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12653 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12654 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12655 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12656 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12657 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12658 chi hbad
              ·
                exact predecessorHalfFin13_clause12660 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12664 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12665 chi hbad
              ·
                exact predecessorHalfFin13_clause12666 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12669 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12671 chi hbad
              ·
                exact predecessorHalfFin13_clause12672 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12673 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12674 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12675 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12676 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12677 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12678 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12679 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12680 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12681 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12682 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12684 chi hbad
              ·
                exact predecessorHalfFin13_clause12686 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12688 chi hbad
              ·
                exact predecessorHalfFin13_clause12689 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12690 chi hbad
              ·
                exact predecessorHalfFin13_clause12693 chi hbad
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
              exact predecessorHalfFin13_clause12695 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12696 chi hbad
              ·
                exact predecessorHalfFin13_clause12697 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12698 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12699 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12700 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12701 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12702 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12703 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12704 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12705 chi hbad
              ·
                exact predecessorHalfFin13_clause12706 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12708 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12712 chi hbad
              ·
                exact predecessorHalfFin13_clause12713 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12715 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12717 chi hbad
              ·
                exact predecessorHalfFin13_clause12719 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12720 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12721 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12722 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12723 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12724 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12725 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12726 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12727 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12728 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12729 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12730 chi hbad
              ·
                exact predecessorHalfFin13_clause12732 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12736 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12737 chi hbad
              ·
                exact predecessorHalfFin13_clause12741 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12742 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12743 chi hbad
              ·
                exact predecessorHalfFin13_clause12744 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12745 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12746 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12747 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12748 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12749 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12750 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12751 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12752 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12753 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12754 chi hbad
              ·
                exact predecessorHalfFin13_clause12756 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12759 chi hbad
              ·
                exact predecessorHalfFin13_clause12760 chi hbad

end ErdosSzekeres

end
