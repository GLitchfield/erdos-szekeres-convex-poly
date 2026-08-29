module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk029
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk030

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 039. -/

theorem predecessorHalfFin13_rejectSemanticSegment039
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0268 chi) ∨
      ((PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0268 chi) ∨
      (¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi))) ∨
      ((¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0773 chi) ∨
      ((¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0773 chi) ∨
      (¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0773 chi) ∨
      ((¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0773 chi) ∨
      (PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0773 chi))) ∨
      ((PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0773 chi) ∨
      ((PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0773 chi) ∨
      (PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi))))) ∨
      ((((PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0773 chi) ∨
      ((PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) ∨
      (¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi))) ∨
      ((¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) ∨
      ((¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0269 chi) ∨
      (¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi)))) ∨
      (((PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0269 chi) ∨
      ((PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) ∨
      (PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0269 chi))) ∨
      ((PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0269 chi) ∨
      ((¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi) ∨
      (¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0774 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi) ∨
      ((¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0774 chi) ∨
      (PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0774 chi))) ∨
      ((PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi) ∨
      ((PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0774 chi) ∨
      (PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) ∨
      ((¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) ∨
      (¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0270 chi))) ∨
      ((¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) ∨
      ((PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      (PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi))))) ∨
      ((((PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      ((PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0270 chi) ∨
      (¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi))) ∨
      ((¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0775 chi) ∨
      ((¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0775 chi) ∨
      (¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0775 chi) ∨
      ((PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0775 chi) ∨
      (PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi))) ∨
      (((PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0775 chi) ∨
      (PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi)) ∨
      ((¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) ∨
      (¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0271 chi) ∨
      ((¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) ∨
      (PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0271 chi))) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0271 chi) ∨
      (PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0271 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) ∨
      ((¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0776 chi) ∨
      (¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0776 chi))) ∨
      ((¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) ∨
      ((¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0776 chi) ∨
      (¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0776 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0776 chi) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0776 chi) ∨
      (PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0776 chi))) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0776 chi) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) ∨
      (PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0776 chi)))) ∨
      (((PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) ∨
      ((¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi) ∨
      (¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi))) ∨
      (((¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0272 chi) ∨
      (¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi)) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0272 chi) ∨
      (PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0272 chi) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0272 chi) ∨
      (¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi))) ∨
      ((¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0777 chi) ∨
      ((¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0777 chi) ∨
      (¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0777 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0777 chi) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0777 chi) ∨
      (PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi))) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0777 chi) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi) ∨
      (¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) ∨
      ((¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0273 chi) ∨
      (¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi))) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0273 chi) ∨
      ((PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) ∨
      (PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0273 chi)))) ∨
      (((PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0273 chi) ∨
      ((¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) ∨
      (¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0778 chi))) ∨
      (((¬PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) ∨
      (¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0778 chi)) ∨
      ((¬PredecessorHalfFin13Atom0153 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0778 chi) ∨
      (PredecessorHalfFin13Atom0153 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0778 chi))))))))) := by
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
              exact predecessorHalfFin13_clause11671 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11672 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11673 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11674 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11675 chi hbad
              ·
                exact predecessorHalfFin13_clause11676 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11679 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11680 chi hbad
              ·
                exact predecessorHalfFin13_clause11681 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11683 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11684 chi hbad
              ·
                exact predecessorHalfFin13_clause11685 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11687 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11688 chi hbad
              ·
                exact predecessorHalfFin13_clause11689 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11690 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11691 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11692 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11693 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11694 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11695 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11696 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11697 chi hbad
              ·
                exact predecessorHalfFin13_clause11698 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11700 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11704 chi hbad
              ·
                exact predecessorHalfFin13_clause11705 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11709 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11711 chi hbad
              ·
                exact predecessorHalfFin13_clause11712 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11713 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11714 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11715 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11716 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11717 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11718 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11719 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11720 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11721 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11722 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11723 chi hbad
              ·
                exact predecessorHalfFin13_clause11724 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11728 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11729 chi hbad
              ·
                exact predecessorHalfFin13_clause11733 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11735 chi hbad
              ·
                exact predecessorHalfFin13_clause11736 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11737 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11738 chi hone hbad
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
              exact predecessorHalfFin13_clause11739 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11740 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11741 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11742 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11743 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11744 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11745 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11746 chi hbad
              ·
                exact predecessorHalfFin13_clause11747 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11748 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11750 chi hbad
              ·
                exact predecessorHalfFin13_clause11751 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11752 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11753 chi hbad
              ·
                exact predecessorHalfFin13_clause11754 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11756 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11757 chi hbad
              ·
                exact predecessorHalfFin13_clause11759 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11760 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11761 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11762 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11763 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11764 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11765 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11766 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11767 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11768 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11769 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11770 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11771 chi hbad
              ·
                exact predecessorHalfFin13_clause11774 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11776 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11777 chi hbad
              ·
                exact predecessorHalfFin13_clause11781 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11783 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11784 chi hbad
              ·
                exact predecessorHalfFin13_clause11785 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11786 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11787 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11788 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11789 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11790 chi hone hbad
              ·
                exact predecessorHalfFin13_clause11791 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause11792 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11793 chi hbad
              ·
                exact predecessorHalfFin13_clause11794 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11796 chi hbad
              ·
                exact predecessorHalfFin13_clause11798 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause11800 chi hbad
              ·
                exact predecessorHalfFin13_clause11801 chi hbad

end ErdosSzekeres

end
