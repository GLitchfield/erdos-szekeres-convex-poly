module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk043
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk044

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 057. -/

theorem predecessorHalfFin13_rejectSemanticSegment057
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      ((¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      (¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi))) ∨
      ((¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      ((PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      (PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi)))) ∨
      (((PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      ((PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      (¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi))) ∨
      ((¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0875 chi) ∨
      ((¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) ∨
      (¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0875 chi))))) ∨
      ((((PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0875 chi) ∨
      ((PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0875 chi) ∨
      (PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi))) ∨
      ((PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0875 chi) ∨
      ((PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi))) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0876 chi))) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0876 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0876 chi)))) ∨
      (((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0876 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi))) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0232 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0232 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi))) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0232 chi) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0232 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0877 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0877 chi))) ∨
      (((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0877 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0877 chi)) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0877 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi))) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0233 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0233 chi)))) ∨
      (((PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0233 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0233 chi))) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0878 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0878 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0878 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0878 chi))) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0878 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0234 chi))) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0234 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0234 chi) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0234 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi))) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0879 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0879 chi)))) ∨
      (((PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0879 chi) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0879 chi))) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0207 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0235 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0235 chi))) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0235 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0235 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) ∨
      ((¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0880 chi) ∨
      (¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi))) ∨
      (((¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0880 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0880 chi)) ∨
      ((PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) ∨
      (PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0208 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0880 chi))))))))) := by
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
              exact predecessorHalfFin13_clause14113 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14114 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14115 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14116 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14117 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14118 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14119 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14120 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14121 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14122 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14124 chi hbad
              ·
                exact predecessorHalfFin13_clause14128 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14129 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14132 chi hbad
              ·
                exact predecessorHalfFin13_clause14133 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14135 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14136 chi hbad
              ·
                exact predecessorHalfFin13_clause14137 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14138 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14139 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14140 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14141 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14142 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14143 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14144 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14145 chi hbad
              ·
                exact predecessorHalfFin13_clause14146 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14148 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14152 chi hbad
              ·
                exact predecessorHalfFin13_clause14153 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14157 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14159 chi hbad
              ·
                exact predecessorHalfFin13_clause14160 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14161 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14162 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14163 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14164 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14165 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14166 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14167 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14168 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14169 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14170 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14172 chi hbad
              ·
                exact predecessorHalfFin13_clause14174 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14176 chi hbad
              ·
                exact predecessorHalfFin13_clause14177 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14181 chi hbad
              ·
                exact predecessorHalfFin13_clause14183 chi hbad
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
              exact predecessorHalfFin13_clause14184 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14185 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14186 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14187 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14188 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14189 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14190 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14191 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14192 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14193 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14194 chi hbad
              ·
                exact predecessorHalfFin13_clause14195 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14196 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14200 chi hbad
              ·
                exact predecessorHalfFin13_clause14201 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14205 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14207 chi hbad
              ·
                exact predecessorHalfFin13_clause14208 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14209 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14210 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14211 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14212 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14213 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14214 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14215 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14216 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14217 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14218 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14220 chi hbad
              ·
                exact predecessorHalfFin13_clause14224 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14225 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14229 chi hbad
              ·
                exact predecessorHalfFin13_clause14231 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14232 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14233 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14234 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14235 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14236 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14237 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14238 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14239 chi hone hbad
              ·
                exact predecessorHalfFin13_clause14240 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause14241 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14242 chi hbad
              ·
                exact predecessorHalfFin13_clause14244 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14248 chi hbad
              ·
                exact predecessorHalfFin13_clause14249 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause14253 chi hbad
              ·
                exact predecessorHalfFin13_clause14255 chi hbad

end ErdosSzekeres

end
