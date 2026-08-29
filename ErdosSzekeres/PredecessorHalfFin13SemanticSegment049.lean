module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk037
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk038

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 049. -/

theorem predecessorHalfFin13_rejectSemanticSegment049
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0829 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0829 chi))) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0241 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0241 chi))) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0241 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0241 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0830 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi))) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0830 chi) ∨
      ((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0830 chi) ∨
      (¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0830 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0830 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0830 chi) ∨
      (PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi))) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0830 chi) ∨
      ((PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0242 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi))) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0242 chi) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi) ∨
      (PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0242 chi)))) ∨
      (((PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0242 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0831 chi))) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0831 chi) ∨
      (PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0831 chi))))) ∨
      ((((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0831 chi) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) ∨
      (PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0831 chi))) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi) ∨
      (PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi))) ∨
      (((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi) ∨
      (PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi)) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0832 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0832 chi))) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0832 chi) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) ∨
      (PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0832 chi)))) ∨
      (((PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi))) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi) ∨
      (PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi))))) ∨
      ((((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi) ∨
      (PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi))) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi))) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) ∨
      (PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0833 chi) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi))) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi)))) ∨
      (((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) ∨
      (PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi))) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0834 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) ∨
      ((¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0834 chi) ∨
      (¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0834 chi))) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0834 chi) ∨
      ((PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) ∨
      (PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0834 chi)))) ∨
      (((PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) ∨
      ((¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) ∨
      (¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi))) ∨
      (((¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi) ∨
      (¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi)) ∨
      ((PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0246 chi) ∨
      (PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi))))))))) := by
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
              exact predecessorHalfFin13_clause13026 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13029 chi hbad
              ·
                exact predecessorHalfFin13_clause13031 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13032 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13033 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13034 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13035 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13036 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13037 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13038 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13039 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13040 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13041 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13042 chi hbad
              ·
                exact predecessorHalfFin13_clause13044 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13045 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13046 chi hbad
              ·
                exact predecessorHalfFin13_clause13047 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13048 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13049 chi hbad
              ·
                exact predecessorHalfFin13_clause13053 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13055 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13056 chi hbad
              ·
                exact predecessorHalfFin13_clause13057 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13058 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13059 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13060 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13061 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13062 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13063 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13064 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13065 chi hbad
              ·
                exact predecessorHalfFin13_clause13066 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13068 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13072 chi hbad
              ·
                exact predecessorHalfFin13_clause13073 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13074 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13077 chi hbad
              ·
                exact predecessorHalfFin13_clause13079 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13080 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13081 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13082 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13083 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13084 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13085 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13086 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13087 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13088 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13089 chi hbad
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
              exact predecessorHalfFin13_clause13090 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13092 chi hbad
              ·
                exact predecessorHalfFin13_clause13096 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13097 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13101 chi hbad
              ·
                exact predecessorHalfFin13_clause13103 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13104 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13105 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13106 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13107 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13108 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13109 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13110 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13111 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13112 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13113 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13114 chi hbad
              ·
                exact predecessorHalfFin13_clause13116 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13117 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13119 chi hbad
              ·
                exact predecessorHalfFin13_clause13120 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13121 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13122 chi hbad
              ·
                exact predecessorHalfFin13_clause13125 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13127 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13128 chi hbad
              ·
                exact predecessorHalfFin13_clause13129 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13130 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13131 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13132 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13133 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13134 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13135 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13136 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13137 chi hbad
              ·
                exact predecessorHalfFin13_clause13138 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13140 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13141 chi hbad
              ·
                exact predecessorHalfFin13_clause13144 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13145 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13149 chi hbad
              ·
                exact predecessorHalfFin13_clause13151 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause13152 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13153 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13154 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13155 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13156 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause13157 chi hone hbad
              ·
                exact predecessorHalfFin13_clause13158 chi hone hbad

end ErdosSzekeres

end
