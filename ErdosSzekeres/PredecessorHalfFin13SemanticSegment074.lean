module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk056
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk057

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 074. -/

theorem predecessorHalfFin13_rejectSemanticSegment074
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0971 chi) ∨
      (PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi))) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi) ∨
      (¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0272 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0272 chi) ∨
      (PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi))) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0272 chi) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0272 chi) ∨
      (¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0972 chi) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) ∨
      (¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0972 chi))) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0972 chi) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0972 chi) ∨
      (PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0972 chi)))) ∨
      (((PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0972 chi) ∨
      (PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi))) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) ∨
      (¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi) ∨
      (PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi))) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi) ∨
      (¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) ∨
      (¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi))) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) ∨
      ((¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) ∨
      (PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi))))) ∨
      ((((PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) ∨
      (PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi))) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) ∨
      ((PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) ∨
      (¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) ∨
      ((¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi) ∨
      (¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi))) ∨
      (((PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi) ∨
      (PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi)) ∨
      ((PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi) ∨
      (PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) ∨
      ((¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0974 chi) ∨
      (¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi))) ∨
      ((¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0974 chi) ∨
      ((PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0974 chi) ∨
      (PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0974 chi)))) ∨
      (((PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) ∨
      ((PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0974 chi) ∨
      (PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi))) ∨
      ((¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) ∨
      ((¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) ∨
      (¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) ∨
      ((PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi) ∨
      (PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi))) ∨
      ((PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi) ∨
      ((PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi) ∨
      (¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0975 chi) ∨
      ((¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) ∨
      (¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0975 chi))) ∨
      ((PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0975 chi) ∨
      ((PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) ∨
      (PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0975 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) ∨
      ((¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) ∨
      (¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi))) ∨
      ((¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi) ∨
      ((¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) ∨
      (PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi)))) ∨
      (((PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) ∨
      ((PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi) ∨
      (PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi))) ∨
      ((¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) ∨
      ((¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0976 chi) ∨
      (¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0976 chi) ∨
      ((PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0976 chi) ∨
      (PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi))) ∨
      ((PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0976 chi) ∨
      ((PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) ∨
      (¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) ∨
      ((¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      (¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi))) ∨
      (((PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      (PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi)) ∨
      ((PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      (PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi))))))))) := by
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
              exact predecessorHalfFin13_clause16437 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16439 chi hbad
              ·
                exact predecessorHalfFin13_clause16440 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16441 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16442 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16443 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16444 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16445 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16446 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16447 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16448 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16449 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16450 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16452 chi hbad
              ·
                exact predecessorHalfFin13_clause16454 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16456 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16457 chi hbad
              ·
                exact predecessorHalfFin13_clause16460 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16461 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16463 chi hbad
              ·
                exact predecessorHalfFin13_clause16464 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16465 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16466 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16467 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16468 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16469 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16470 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16471 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16472 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16473 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16474 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16476 chi hbad
              ·
                exact predecessorHalfFin13_clause16477 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16478 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16480 chi hbad
              ·
                exact predecessorHalfFin13_clause16481 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16482 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16484 chi hbad
              ·
                exact predecessorHalfFin13_clause16485 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16487 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16488 chi hbad
              ·
                exact predecessorHalfFin13_clause16489 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16490 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16491 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16492 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16493 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16494 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16495 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16496 chi hone hbad
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
              exact predecessorHalfFin13_clause16497 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16498 chi hbad
              ·
                exact predecessorHalfFin13_clause16500 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16504 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16505 chi hbad
              ·
                exact predecessorHalfFin13_clause16506 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16509 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16511 chi hbad
              ·
                exact predecessorHalfFin13_clause16512 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16513 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16514 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16515 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16516 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16517 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16518 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16519 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16520 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16521 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16522 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16524 chi hbad
              ·
                exact predecessorHalfFin13_clause16528 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16529 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16533 chi hbad
              ·
                exact predecessorHalfFin13_clause16535 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16536 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16537 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16538 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16539 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16540 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16541 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16542 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16543 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16544 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16545 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16546 chi hbad
              ·
                exact predecessorHalfFin13_clause16548 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16552 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16553 chi hbad
              ·
                exact predecessorHalfFin13_clause16557 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16559 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16560 chi hbad
              ·
                exact predecessorHalfFin13_clause16561 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause16562 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16563 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16564 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16565 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16566 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause16567 chi hone hbad
              ·
                exact predecessorHalfFin13_clause16568 chi hone hbad

end ErdosSzekeres

end
