module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk052
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk053

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 069. -/

theorem predecessorHalfFin13_rejectSemanticSegment069
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) ∨
      ((¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0943 chi) ∨
      (¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi))) ∨
      ((¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0943 chi) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0943 chi) ∨
      (PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi)))) ∨
      (((PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0943 chi) ∨
      ((PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0943 chi) ∨
      (PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi))) ∨
      ((¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi) ∨
      ((¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi) ∨
      (¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi) ∨
      ((PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi) ∨
      (PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi))) ∨
      ((PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi) ∨
      ((PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi) ∨
      (¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0944 chi) ∨
      ((¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) ∨
      (¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0944 chi))) ∨
      ((PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0944 chi) ∨
      ((PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0944 chi) ∨
      (PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0944 chi) ∨
      ((PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) ∨
      (¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi))) ∨
      ((¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) ∨
      ((¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi) ∨
      (¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi)))) ∨
      (((PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi) ∨
      ((PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) ∨
      (PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi))) ∨
      ((PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi) ∨
      ((¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) ∨
      (¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) ∨
      ((¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) ∨
      (¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi))) ∨
      ((¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) ∨
      ((PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) ∨
      (PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi)))) ∨
      (((PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) ∨
      ((PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) ∨
      (PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi))) ∨
      (((¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi) ∨
      (¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi)) ∨
      ((¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi) ∨
      (¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi) ∨
      ((PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi) ∨
      (PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi))) ∨
      ((PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi) ∨
      ((¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0946 chi) ∨
      (PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0946 chi)))) ∨
      (((PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0946 chi) ∨
      ((PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0946 chi) ∨
      (PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0946 chi))) ∨
      ((¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) ∨
      ((¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) ∨
      (¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) ∨
      ((PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi) ∨
      (PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi))) ∨
      ((PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi) ∨
      ((PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi) ∨
      (¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi) ∨
      ((¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) ∨
      (¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi))) ∨
      ((¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi) ∨
      ((PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi) ∨
      (PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) ∨
      ((PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi) ∨
      (PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi))) ∨
      ((¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) ∨
      ((¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) ∨
      (¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) ∨
      ((PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi) ∨
      (PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi))) ∨
      ((PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi) ∨
      ((PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi) ∨
      (¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      ((¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) ∨
      (¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi))) ∨
      ((¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      ((¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      (¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi)))) ∨
      (((PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      ((PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      (PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi))) ∨
      (((PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      (PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi)) ∨
      ((¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) ∨
      (¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi))))))))) := by
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
              exact predecessorHalfFin13_clause15753 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15754 chi hbad
              ·
                exact predecessorHalfFin13_clause15756 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15760 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15761 chi hbad
              ·
                exact predecessorHalfFin13_clause15765 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15766 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15767 chi hbad
              ·
                exact predecessorHalfFin13_clause15768 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15769 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15770 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15771 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15772 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15773 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15774 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15775 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15776 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15777 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15778 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15780 chi hbad
              ·
                exact predecessorHalfFin13_clause15784 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15785 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15787 chi hbad
              ·
                exact predecessorHalfFin13_clause15789 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15791 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15792 chi hbad
              ·
                exact predecessorHalfFin13_clause15793 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15794 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15795 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15796 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15797 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15798 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15799 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15800 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15801 chi hbad
              ·
                exact predecessorHalfFin13_clause15802 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15803 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15804 chi hbad
              ·
                exact predecessorHalfFin13_clause15807 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15808 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15809 chi hbad
              ·
                exact predecessorHalfFin13_clause15813 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15814 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15815 chi hbad
              ·
                exact predecessorHalfFin13_clause15816 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15817 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15818 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15819 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15820 chi hone hbad
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
              exact predecessorHalfFin13_clause15821 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15822 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15823 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15824 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15826 chi hbad
              ·
                exact predecessorHalfFin13_clause15833 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15837 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15839 chi hbad
              ·
                exact predecessorHalfFin13_clause15840 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15841 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15842 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15843 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15844 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15845 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15846 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15847 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15848 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15849 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15850 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15852 chi hbad
              ·
                exact predecessorHalfFin13_clause15855 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15856 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15857 chi hbad
              ·
                exact predecessorHalfFin13_clause15859 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15861 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15863 chi hbad
              ·
                exact predecessorHalfFin13_clause15864 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15865 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15866 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15867 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15868 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15869 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15870 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15871 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15872 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15873 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15874 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15876 chi hbad
              ·
                exact predecessorHalfFin13_clause15877 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15878 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15879 chi hbad
              ·
                exact predecessorHalfFin13_clause15880 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15881 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15882 chi hbad
              ·
                exact predecessorHalfFin13_clause15885 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15887 chi hbad
              ·
                exact predecessorHalfFin13_clause15888 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15889 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15890 chi hone hbad

end ErdosSzekeres

end
