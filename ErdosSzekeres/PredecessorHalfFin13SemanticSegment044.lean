module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk033
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk034

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 044. -/

theorem predecessorHalfFin13_rejectSemanticSegment044
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0801 chi) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0801 chi) ∨
      (PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi))) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0801 chi) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) ∨
      (¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi) ∨
      (¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi))) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) ∨
      (PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi))))) ∨
      ((((PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) ∨
      (¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0802 chi))) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0802 chi) ∨
      (PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0802 chi)))) ∨
      (((PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0802 chi) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) ∨
      (PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0802 chi))) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) ∨
      (¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0214 chi) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) ∨
      (PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0214 chi))) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0214 chi) ∨
      (PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0214 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0803 chi) ∨
      (¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0803 chi))) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0803 chi) ∨
      (PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0803 chi))))) ∨
      ((((PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0803 chi) ∨
      (PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0173 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi))) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) ∨
      (¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0215 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0215 chi) ∨
      (PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi))) ∨
      (((PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0215 chi) ∨
      (PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0215 chi)) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) ∨
      (¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0804 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) ∨
      ((¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0804 chi) ∨
      (¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0804 chi))) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0804 chi) ∨
      ((PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) ∨
      (PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0804 chi)))) ∨
      (((PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0174 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi))) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0216 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0216 chi))))) ∨
      ((((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0216 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0216 chi))) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0805 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0805 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0805 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0805 chi))) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0805 chi) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0805 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0805 chi) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi))) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0217 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi)))) ∨
      (((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0217 chi) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0217 chi))) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0217 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0806 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0806 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0806 chi))) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0806 chi) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0806 chi)))) ∨
      (((PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) ∨
      ((¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi))) ∨
      (((¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0218 chi) ∨
      (¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi)) ∨
      ((PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0218 chi) ∨
      (PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi))))))))) := by
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
              exact predecessorHalfFin13_clause12352 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12353 chi hbad
              ·
                exact predecessorHalfFin13_clause12357 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12359 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12360 chi hbad
              ·
                exact predecessorHalfFin13_clause12361 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12362 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12363 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12364 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12365 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12366 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12367 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12368 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12369 chi hbad
              ·
                exact predecessorHalfFin13_clause12370 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12372 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12376 chi hbad
              ·
                exact predecessorHalfFin13_clause12377 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12380 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12381 chi hbad
              ·
                exact predecessorHalfFin13_clause12383 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12384 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12385 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12386 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12387 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12388 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12389 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12390 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12391 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12392 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12393 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12394 chi hbad
              ·
                exact predecessorHalfFin13_clause12395 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12396 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12400 chi hbad
              ·
                exact predecessorHalfFin13_clause12401 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12405 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12407 chi hbad
              ·
                exact predecessorHalfFin13_clause12408 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12409 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12410 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12411 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12412 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12413 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12414 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12415 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12416 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12417 chi hbad
              ·
                exact predecessorHalfFin13_clause12418 chi hbad
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
              exact predecessorHalfFin13_clause12420 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12422 chi hbad
              ·
                exact predecessorHalfFin13_clause12424 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12425 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12429 chi hbad
              ·
                exact predecessorHalfFin13_clause12431 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12432 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12433 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12434 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12435 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12436 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12437 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12438 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12439 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12440 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12441 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12442 chi hbad
              ·
                exact predecessorHalfFin13_clause12444 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12446 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12448 chi hbad
              ·
                exact predecessorHalfFin13_clause12449 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12451 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12453 chi hbad
              ·
                exact predecessorHalfFin13_clause12454 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12455 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12456 chi hbad
              ·
                exact predecessorHalfFin13_clause12457 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12458 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12459 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12460 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12461 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12462 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12463 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12464 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12465 chi hbad
              ·
                exact predecessorHalfFin13_clause12466 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12468 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12472 chi hbad
              ·
                exact predecessorHalfFin13_clause12473 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12475 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12477 chi hbad
              ·
                exact predecessorHalfFin13_clause12479 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause12480 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12481 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12482 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12483 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12484 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause12485 chi hone hbad
              ·
                exact predecessorHalfFin13_clause12486 chi hone hbad

end ErdosSzekeres

end
