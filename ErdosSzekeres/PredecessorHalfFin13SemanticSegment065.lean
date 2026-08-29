module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk049
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk050

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 065. -/

theorem predecessorHalfFin13_rejectSemanticSegment065
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) ∨
      ((PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi) ∨
      (PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi))) ∨
      ((PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi) ∨
      ((PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi) ∨
      (¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0920 chi) ∨
      ((¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) ∨
      (¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0920 chi))) ∨
      ((PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0920 chi) ∨
      ((PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0920 chi) ∨
      (PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi))))) ∨
      ((((PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0920 chi) ∨
      ((PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) ∨
      (¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi))) ∨
      ((¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) ∨
      ((¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0276 chi) ∨
      (¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi)))) ∨
      (((PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0276 chi) ∨
      ((PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) ∨
      (PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0276 chi))) ∨
      ((PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0276 chi) ∨
      ((¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) ∨
      (¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0921 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) ∨
      ((¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0921 chi) ∨
      (PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi))) ∨
      ((PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0921 chi) ∨
      ((PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) ∨
      (¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      (¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi))) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) ∨
      (PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0277 chi))))) ∨
      ((((PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0277 chi) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) ∨
      (¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0922 chi))) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0922 chi) ∨
      (¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0922 chi)))) ∨
      (((PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0922 chi) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0922 chi) ∨
      (PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi))) ∨
      (((PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0922 chi) ∨
      (PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0922 chi)) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) ∨
      (¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0278 chi) ∨
      (¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi))) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0278 chi) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) ∨
      (PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0278 chi)))) ∨
      (((PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0278 chi) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) ∨
      (¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0923 chi))) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0923 chi) ∨
      (PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0923 chi))))) ∨
      ((((PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0923 chi) ∨
      (PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi))) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) ∨
      (¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0279 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0279 chi) ∨
      (PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi))) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0279 chi) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0279 chi) ∨
      (¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0924 chi) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) ∨
      (¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0924 chi))) ∨
      ((¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0924 chi) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0924 chi) ∨
      (PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi)))) ∨
      (((PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0924 chi) ∨
      ((PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) ∨
      (¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi))) ∨
      ((¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) ∨
      ((¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0280 chi) ∨
      (¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi))))) ∨
      ((((PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0280 chi) ∨
      ((PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) ∨
      (PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0280 chi))) ∨
      ((PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0280 chi) ∨
      ((¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) ∨
      (¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0925 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) ∨
      ((¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0925 chi) ∨
      (¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0925 chi))) ∨
      (((PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0925 chi) ∨
      (PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi)) ∨
      ((PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0925 chi) ∨
      (PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0925 chi))))))))) := by
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
              exact predecessorHalfFin13_clause15196 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15197 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15198 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15199 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15200 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15201 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15202 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15204 chi hbad
              ·
                exact predecessorHalfFin13_clause15208 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15209 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15212 chi hbad
              ·
                exact predecessorHalfFin13_clause15213 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15215 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15216 chi hbad
              ·
                exact predecessorHalfFin13_clause15217 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15218 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15219 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15220 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15221 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15222 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15223 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15224 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15225 chi hbad
              ·
                exact predecessorHalfFin13_clause15226 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15228 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15232 chi hbad
              ·
                exact predecessorHalfFin13_clause15237 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15239 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15240 chi hbad
              ·
                exact predecessorHalfFin13_clause15241 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15242 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15243 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15244 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15245 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15246 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15247 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15248 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15249 chi hbad
              ·
                exact predecessorHalfFin13_clause15250 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15252 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15253 chi hbad
              ·
                exact predecessorHalfFin13_clause15256 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15257 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15258 chi hbad
              ·
                exact predecessorHalfFin13_clause15261 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15262 chi hbad
              ·
                exact predecessorHalfFin13_clause15263 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15264 chi hbad
              ·
                exact predecessorHalfFin13_clause15265 chi hone hbad
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
              exact predecessorHalfFin13_clause15266 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15267 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15268 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15269 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15270 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15271 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15272 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15273 chi hbad
              ·
                exact predecessorHalfFin13_clause15274 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15276 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15280 chi hbad
              ·
                exact predecessorHalfFin13_clause15281 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15285 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15287 chi hbad
              ·
                exact predecessorHalfFin13_clause15288 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15289 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15290 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15291 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15292 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15293 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15294 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15295 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15296 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15297 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15298 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15300 chi hbad
              ·
                exact predecessorHalfFin13_clause15302 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15304 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15305 chi hbad
              ·
                exact predecessorHalfFin13_clause15309 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15311 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15312 chi hbad
              ·
                exact predecessorHalfFin13_clause15313 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15314 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15315 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15316 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15317 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15318 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15319 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15320 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15321 chi hbad
              ·
                exact predecessorHalfFin13_clause15322 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15324 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15326 chi hbad
              ·
                exact predecessorHalfFin13_clause15328 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15329 chi hbad
              ·
                exact predecessorHalfFin13_clause15333 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15334 chi hbad
              ·
                exact predecessorHalfFin13_clause15335 chi hbad

end ErdosSzekeres

end
