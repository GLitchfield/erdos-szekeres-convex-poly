module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk038
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk039

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 050. -/

theorem predecessorHalfFin13_rejectSemanticSegment050
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi) ∨
      (¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi))) ∨
      ((¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0835 chi) ∨
      ((¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) ∨
      (¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0835 chi)))) ∨
      (((PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0835 chi) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0835 chi) ∨
      (PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi))) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0835 chi) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) ∨
      (¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi) ∨
      ((¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi) ∨
      (¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi))) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi) ∨
      (PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi)))) ∨
      (((PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi) ∨
      ((¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) ∨
      (¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0836 chi))) ∨
      ((¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) ∨
      ((¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0836 chi) ∨
      (PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0836 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0836 chi) ∨
      (PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi))) ∨
      ((¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) ∨
      ((¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) ∨
      (¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi) ∨
      (PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi))) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi) ∨
      (¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0837 chi) ∨
      ((¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) ∨
      (¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0837 chi))) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0837 chi) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0837 chi) ∨
      (PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi)))) ∨
      (((PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0837 chi) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) ∨
      (¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi))) ∨
      (((¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi) ∨
      (¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi)) ∨
      ((¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi) ∨
      (PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi) ∨
      ((PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi) ∨
      (PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi))) ∨
      ((¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) ∨
      ((¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) ∨
      (¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) ∨
      ((¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) ∨
      (¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi))) ∨
      ((PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) ∨
      ((PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) ∨
      (PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi))))) ∨
      ((((PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) ∨
      ((PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0838 chi) ∨
      (PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi))) ∨
      ((¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) ∨
      ((¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) ∨
      (¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) ∨
      ((PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi) ∨
      (PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi))) ∨
      ((PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi) ∨
      ((PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi) ∨
      (¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0839 chi) ∨
      ((¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) ∨
      (¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0839 chi))) ∨
      ((¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0839 chi) ∨
      ((PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0839 chi) ∨
      (PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi)))) ∨
      (((PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0839 chi) ∨
      ((PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) ∨
      (¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi))) ∨
      ((¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi) ∨
      ((¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi) ∨
      (¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi))))) ∨
      ((((PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi) ∨
      ((PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi) ∨
      (PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi))) ∨
      ((PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi) ∨
      ((¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) ∨
      (¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0840 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) ∨
      ((¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0840 chi) ∨
      (¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0840 chi))) ∨
      (((PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0840 chi) ∨
      (PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi)) ∨
      ((PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) ∨
      (¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi))))))))) := by
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
              exact predecessorHalfFin13_clause13159 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13160 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13161 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13162 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13164 chi hbad
              ·
                exact predecessorHalfFin13_clause13168 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13169 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13170 chi hbad
              ·
                exact predecessorHalfFin13_clause13173 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13175 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13176 chi hbad
              ·
                exact predecessorHalfFin13_clause13177 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13178 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13179 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13180 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13181 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13182 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13183 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13184 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13185 chi hbad
              ·
                exact predecessorHalfFin13_clause13186 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13188 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13192 chi hbad
              ·
                exact predecessorHalfFin13_clause13193 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13197 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13199 chi hbad
              ·
                exact predecessorHalfFin13_clause13200 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13201 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13202 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13203 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13204 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13205 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13206 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13207 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13208 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13209 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13210 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13212 chi hbad
              ·
                exact predecessorHalfFin13_clause13216 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13217 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13218 chi hbad
              ·
                exact predecessorHalfFin13_clause13221 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13223 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13224 chi hbad
              ·
                exact predecessorHalfFin13_clause13225 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13226 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13227 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13228 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13229 chi hone hbad
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
              exact predecessorHalfFin13_clause13230 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13231 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13232 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13233 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13234 chi hbad
              ·
                exact predecessorHalfFin13_clause13236 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13238 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13239 chi hbad
              ·
                exact predecessorHalfFin13_clause13240 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13241 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13242 chi hbad
              ·
                exact predecessorHalfFin13_clause13243 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13245 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13247 chi hbad
              ·
                exact predecessorHalfFin13_clause13248 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13249 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13250 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13251 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13252 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13253 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13254 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13255 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13256 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13257 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13258 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13260 chi hbad
              ·
                exact predecessorHalfFin13_clause13263 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13264 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13265 chi hbad
              ·
                exact predecessorHalfFin13_clause13269 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13271 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13272 chi hbad
              ·
                exact predecessorHalfFin13_clause13273 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13274 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13275 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13276 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13277 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13278 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13279 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13280 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13281 chi hbad
              ·
                exact predecessorHalfFin13_clause13282 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13284 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13287 chi hbad
              ·
                exact predecessorHalfFin13_clause13288 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13289 chi hbad
              ·
                exact predecessorHalfFin13_clause13293 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13296 chi hbad
              ·
                exact predecessorHalfFin13_clause13297 chi hone hbad

end ErdosSzekeres

end
