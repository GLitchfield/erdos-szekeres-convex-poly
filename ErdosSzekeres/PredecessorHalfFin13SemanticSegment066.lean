module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk050
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk051

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 066. -/

theorem predecessorHalfFin13_rejectSemanticSegment066
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) ∨
      ((¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) ∨
      (¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi))) ∨
      ((¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0281 chi) ∨
      ((¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) ∨
      (PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0281 chi)))) ∨
      (((PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) ∨
      ((PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0281 chi) ∨
      (PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0281 chi))) ∨
      ((¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) ∨
      ((¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0926 chi) ∨
      (¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0926 chi) ∨
      ((PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0926 chi) ∨
      (PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi))) ∨
      ((PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0926 chi) ∨
      ((PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) ∨
      (¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) ∨
      ((¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0282 chi) ∨
      (¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi))) ∨
      ((PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0282 chi) ∨
      ((PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) ∨
      (PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0282 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0282 chi) ∨
      ((¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi) ∨
      (¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0927 chi))) ∨
      ((¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi) ∨
      ((¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0927 chi) ∨
      (PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi)))) ∨
      (((PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0927 chi) ∨
      ((PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi) ∨
      (¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi))) ∨
      ((¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) ∨
      ((¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi) ∨
      (¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi))))) ∨
      ((((PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi) ∨
      ((PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) ∨
      (PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi))) ∨
      ((PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi) ∨
      ((¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) ∨
      (¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0928 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) ∨
      ((¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0928 chi) ∨
      (¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0928 chi))) ∨
      (((PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0928 chi) ∨
      (PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi)) ∨
      ((PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0928 chi) ∨
      (PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) ∨
      ((¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) ∨
      (¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi))) ∨
      ((¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) ∨
      ((PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi) ∨
      (PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi)))) ∨
      (((PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi) ∨
      ((PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi) ∨
      (¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi))) ∨
      ((¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi) ∨
      ((¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi) ∨
      (¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi) ∨
      ((PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi) ∨
      (PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi))) ∨
      ((PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) ∨
      ((PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi) ∨
      (PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi)))) ∨
      (((¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) ∨
      ((¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) ∨
      (¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi))) ∨
      ((¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) ∨
      ((PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi) ∨
      (PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi) ∨
      ((PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi) ∨
      (¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi))) ∨
      ((¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi) ∨
      ((¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) ∨
      (¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi)))) ∨
      (((PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi) ∨
      ((PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi) ∨
      (PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi))) ∨
      ((PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi) ∨
      ((PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) ∨
      (PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi))))) ∨
      ((((PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) ∨
      ((¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      (¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi))) ∨
      ((¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      ((¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      (PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi)))) ∨
      (((PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) ∨
      ((PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi) ∨
      (PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi))) ∨
      (((¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) ∨
      (¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0931 chi)) ∨
      ((¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) ∨
      (¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0931 chi))))))))) := by
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
              exact predecessorHalfFin13_clause15336 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15337 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15338 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15339 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15340 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15341 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15342 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15343 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15344 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15345 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15346 chi hbad
              ·
                exact predecessorHalfFin13_clause15348 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15352 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15353 chi hbad
              ·
                exact predecessorHalfFin13_clause15357 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15359 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15360 chi hbad
              ·
                exact predecessorHalfFin13_clause15361 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15362 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15363 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15364 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15365 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15366 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15367 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15368 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15369 chi hbad
              ·
                exact predecessorHalfFin13_clause15370 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15372 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15376 chi hbad
              ·
                exact predecessorHalfFin13_clause15381 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15383 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15384 chi hbad
              ·
                exact predecessorHalfFin13_clause15385 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15386 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15387 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15388 chi hone hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15389 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15390 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15391 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15392 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15393 chi hbad
              ·
                exact predecessorHalfFin13_clause15394 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15396 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15399 chi hbad
              ·
                exact predecessorHalfFin13_clause15400 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15401 chi hbad
              ·
                exact predecessorHalfFin13_clause15405 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15407 chi hbad
              ·
                exact predecessorHalfFin13_clause15408 chi hbad
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
              exact predecessorHalfFin13_clause15409 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15410 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15411 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15412 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15413 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15414 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15415 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15416 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15417 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15418 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15419 chi hbad
              ·
                exact predecessorHalfFin13_clause15420 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15424 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15425 chi hbad
              ·
                exact predecessorHalfFin13_clause15428 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15429 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15431 chi hbad
              ·
                exact predecessorHalfFin13_clause15432 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15433 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15434 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15435 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15436 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15437 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15438 chi hone hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15439 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15440 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15441 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15442 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15444 chi hbad
              ·
                exact predecessorHalfFin13_clause15448 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15449 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15450 chi hbad
              ·
                exact predecessorHalfFin13_clause15451 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15452 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15453 chi hbad
              ·
                exact predecessorHalfFin13_clause15455 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15456 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15457 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15458 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15459 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15460 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15461 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause15462 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15463 chi hone hbad
              ·
                exact predecessorHalfFin13_clause15464 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15465 chi hbad
              ·
                exact predecessorHalfFin13_clause15466 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause15468 chi hbad
              ·
                exact predecessorHalfFin13_clause15470 chi hbad

end ErdosSzekeres

end
