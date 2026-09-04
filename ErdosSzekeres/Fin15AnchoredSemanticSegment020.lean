module

public import ErdosSzekeres.Fin15AnchoredClauseChunk039
public import ErdosSzekeres.Fin15AnchoredClauseChunk040
public import ErdosSzekeres.Fin15AnchoredClauseChunk041

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 020. -/

theorem fin15Anchored_rejectSemanticSegment020
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi) ∨
      ((¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi))) ∨
      (((¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi)) ∨
      ((Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi)))) ∨
      ((((Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi) ∨
      (¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi)) ∨
      ((¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi) ∨
      (¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi))) ∨
      (((¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi) ∨
      (Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi)) ∨
      ((Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi) ∨
      (Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi))))) ∨
      (((((Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi) ∨
      (¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0367 chi)) ∨
      ((¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0367 chi) ∨
      (¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0367 chi))) ∨
      (((Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0367 chi) ∨
      (Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0367 chi)) ∨
      ((Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0367 chi) ∨
      (¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0368 chi)))) ∨
      ((((¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0368 chi) ∨
      (¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0368 chi)) ∨
      ((Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0368 chi) ∨
      (¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi))) ∨
      (((¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi)) ∨
      ((¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi)))))) ∨
      ((((((Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi) ∨
      (Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi)) ∨
      ((Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi) ∨
      (¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi))) ∨
      (((¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi)) ∨
      ((¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi)))) ∨
      ((((Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi) ∨
      (Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi)) ∨
      ((Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi) ∨
      (¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi))) ∨
      (((¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi) ∨
      (¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi)) ∨
      ((¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi) ∨
      (Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi))))) ∨
      (((((Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi) ∨
      (Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi)) ∨
      ((Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi)))) ∨
      ((((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi))))))) ∨
      ((((((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi)))) ∨
      ((((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi))))) ∨
      (((((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi)))) ∨
      ((((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi)))))) ∨
      ((((((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi)))) ∨
      ((((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi))) ∨
      (((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi)) ∨
      ((¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi))))) ∨
      (((((Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0379 chi)) ∨
      ((Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0379 chi))) ∨
      (((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi)) ∨
      ((¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi)))) ∨
      ((((Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0380 chi)) ∨
      ((Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0380 chi))) ∨
      (((¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi)) ∨
      ((¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi) ∨
      ((Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0382 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi))) ∨
      (((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0382 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi)) ∨
      ((¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi)))) ∨
      ((((¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi)) ∨
      ((Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0383 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi))) ∨
      (((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0383 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi)) ∨
      ((¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi) ∨
      (¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi))))) ∨
      (((((¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi)) ∨
      ((Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0384 chi) ∨
      (Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi))) ∨
      (((Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0384 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi)) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi)))) ∨
      ((((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi)) ∨
      ((Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0385 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi))) ∨
      (((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0385 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi)) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi)) ∨
      ((Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0386 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi))) ∨
      (((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0386 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi)) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi)))) ∨
      ((((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi)) ∨
      ((Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0387 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi))) ∨
      (((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi)) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi))))) ∨
      (((((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi)) ∨
      ((Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi))) ∨
      (((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0388 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi)) ∨
      ((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi) ∨
      (¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi)))) ∨
      ((((¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi)) ∨
      ((Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0389 chi) ∨
      (Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi))) ∨
      (((Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0389 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi)) ∨
      ((¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi) ∨
      ((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0390 chi))) ∨
      (((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0390 chi)) ∨
      ((¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi)))) ∨
      ((((¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi)) ∨
      ((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0391 chi))) ∨
      (((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0391 chi)) ∨
      ((¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi))))) ∨
      (((((¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi)) ∨
      ((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0392 chi))) ∨
      (((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0392 chi)) ∨
      ((¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi)))) ∨
      ((((¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi) ∨
      (¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi)) ∨
      ((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0393 chi))) ∨
      (((Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi) ∨
      (Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0393 chi)) ∨
      ((¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi) ∨
      (¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi) ∨
      (¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi)) ∨
      ((Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi) ∨
      (Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0394 chi))) ∨
      (((Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi) ∨
      (Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0394 chi)) ∨
      ((¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi) ∨
      (¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi)))) ∨
      ((((¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi) ∨
      (¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi)) ∨
      ((Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi) ∨
      (Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0395 chi))) ∨
      (((Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi) ∨
      (Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0395 chi)) ∨
      ((¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi) ∨
      (¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi))))) ∨
      (((((¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi) ∨
      (Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0396 chi)) ∨
      ((Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0396 chi) ∨
      (Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0396 chi))) ∨
      (((¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi) ∨
      (¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi)) ∨
      ((¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi)))) ∨
      ((((Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0397 chi)) ∨
      ((Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0397 chi))) ∨
      (((¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi) ∨
      (¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi)) ∨
      ((¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0398 chi)))))))))) := by
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
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause05047 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05048 chi hone hbad
                ·
                  exact fin15Anchored_clause05049 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05050 chi hone hbad
                ·
                  exact fin15Anchored_clause05051 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05052 chi hone hbad
                ·
                  exact fin15Anchored_clause05053 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05054 chi hone hbad
                ·
                  exact fin15Anchored_clause05055 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05056 chi hone hbad
                ·
                  exact fin15Anchored_clause05057 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05058 chi hone hbad
                ·
                  exact fin15Anchored_clause05059 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05060 chi hone hbad
                ·
                  exact fin15Anchored_clause05061 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05062 chi hone hbad
                ·
                  exact fin15Anchored_clause05063 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05064 chi hone hbad
                ·
                  exact fin15Anchored_clause05065 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05066 chi hone hbad
                ·
                  exact fin15Anchored_clause05067 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05068 chi hone hbad
                ·
                  exact fin15Anchored_clause05069 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05070 chi hone hbad
                ·
                  exact fin15Anchored_clause05071 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05072 chi hone hbad
                ·
                  exact fin15Anchored_clause05073 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05074 chi hone hbad
                ·
                  exact fin15Anchored_clause05075 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05076 chi hone hbad
                ·
                  exact fin15Anchored_clause05077 chi hone hbad
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
                  exact fin15Anchored_clause05078 chi hone hbad
                ·
                  exact fin15Anchored_clause05079 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05080 chi hone hbad
                ·
                  exact fin15Anchored_clause05081 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05082 chi hone hbad
                ·
                  exact fin15Anchored_clause05083 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05084 chi hone hbad
                ·
                  exact fin15Anchored_clause05085 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05086 chi hone hbad
                ·
                  exact fin15Anchored_clause05087 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05088 chi hone hbad
                ·
                  exact fin15Anchored_clause05089 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05090 chi hone hbad
                ·
                  exact fin15Anchored_clause05091 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05092 chi hone hbad
                ·
                  exact fin15Anchored_clause05093 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05094 chi hone hbad
                ·
                  exact fin15Anchored_clause05095 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05096 chi hone hbad
                ·
                  exact fin15Anchored_clause05097 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05098 chi hone hbad
                ·
                  exact fin15Anchored_clause05099 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05100 chi hone hbad
                ·
                  exact fin15Anchored_clause05101 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05102 chi hone hbad
                ·
                  exact fin15Anchored_clause05103 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05104 chi hone hbad
                ·
                  exact fin15Anchored_clause05105 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05106 chi hone hbad
                ·
                  exact fin15Anchored_clause05107 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05108 chi hone hbad
                ·
                  exact fin15Anchored_clause05109 chi hone hbad
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
                exact fin15Anchored_clause05110 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05111 chi hone hbad
                ·
                  exact fin15Anchored_clause05112 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05113 chi hone hbad
                ·
                  exact fin15Anchored_clause05114 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05115 chi hone hbad
                ·
                  exact fin15Anchored_clause05116 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05117 chi hone hbad
                ·
                  exact fin15Anchored_clause05118 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05119 chi hone hbad
                ·
                  exact fin15Anchored_clause05120 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05121 chi hone hbad
                ·
                  exact fin15Anchored_clause05122 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05123 chi hone hbad
                ·
                  exact fin15Anchored_clause05124 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05125 chi hone hbad
                ·
                  exact fin15Anchored_clause05126 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05127 chi hone hbad
                ·
                  exact fin15Anchored_clause05128 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05129 chi hone hbad
                ·
                  exact fin15Anchored_clause05130 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05131 chi hone hbad
                ·
                  exact fin15Anchored_clause05132 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05133 chi hone hbad
                ·
                  exact fin15Anchored_clause05134 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05135 chi hone hbad
                ·
                  exact fin15Anchored_clause05136 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05137 chi hone hbad
                ·
                  exact fin15Anchored_clause05138 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05139 chi hone hbad
                ·
                  exact fin15Anchored_clause05140 chi hone hbad
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
                  exact fin15Anchored_clause05141 chi hone hbad
                ·
                  exact fin15Anchored_clause05142 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05143 chi hone hbad
                ·
                  exact fin15Anchored_clause05144 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05145 chi hone hbad
                ·
                  exact fin15Anchored_clause05146 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05147 chi hone hbad
                ·
                  exact fin15Anchored_clause05148 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05149 chi hone hbad
                ·
                  exact fin15Anchored_clause05150 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05151 chi hone hbad
                ·
                  exact fin15Anchored_clause05152 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05153 chi hone hbad
                ·
                  exact fin15Anchored_clause05154 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05155 chi hone hbad
                ·
                  exact fin15Anchored_clause05156 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05157 chi hone hbad
                ·
                  exact fin15Anchored_clause05158 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05159 chi hone hbad
                ·
                  exact fin15Anchored_clause05160 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05161 chi hone hbad
                ·
                  exact fin15Anchored_clause05162 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05163 chi hone hbad
                ·
                  exact fin15Anchored_clause05164 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05165 chi hone hbad
                ·
                  exact fin15Anchored_clause05166 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05167 chi hone hbad
                ·
                  exact fin15Anchored_clause05168 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05169 chi hone hbad
                ·
                  exact fin15Anchored_clause05170 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05171 chi hone hbad
                ·
                  exact fin15Anchored_clause05172 chi hone hbad
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
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause05173 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05174 chi hone hbad
                ·
                  exact fin15Anchored_clause05175 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05176 chi hone hbad
                ·
                  exact fin15Anchored_clause05177 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05178 chi hone hbad
                ·
                  exact fin15Anchored_clause05179 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05180 chi hone hbad
                ·
                  exact fin15Anchored_clause05181 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05182 chi hone hbad
                ·
                  exact fin15Anchored_clause05183 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05184 chi hone hbad
                ·
                  exact fin15Anchored_clause05185 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05186 chi hone hbad
                ·
                  exact fin15Anchored_clause05187 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05188 chi hone hbad
                ·
                  exact fin15Anchored_clause05189 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05190 chi hone hbad
                ·
                  exact fin15Anchored_clause05191 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05192 chi hone hbad
                ·
                  exact fin15Anchored_clause05193 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05194 chi hone hbad
                ·
                  exact fin15Anchored_clause05195 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05196 chi hone hbad
                ·
                  exact fin15Anchored_clause05197 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05198 chi hone hbad
                ·
                  exact fin15Anchored_clause05199 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05200 chi hone hbad
                ·
                  exact fin15Anchored_clause05201 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05202 chi hone hbad
                ·
                  exact fin15Anchored_clause05203 chi hone hbad
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
                  exact fin15Anchored_clause05204 chi hone hbad
                ·
                  exact fin15Anchored_clause05205 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05206 chi hone hbad
                ·
                  exact fin15Anchored_clause05207 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05208 chi hone hbad
                ·
                  exact fin15Anchored_clause05209 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05210 chi hone hbad
                ·
                  exact fin15Anchored_clause05211 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05212 chi hone hbad
                ·
                  exact fin15Anchored_clause05213 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05214 chi hone hbad
                ·
                  exact fin15Anchored_clause05215 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05216 chi hone hbad
                ·
                  exact fin15Anchored_clause05217 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05218 chi hone hbad
                ·
                  exact fin15Anchored_clause05219 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05220 chi hone hbad
                ·
                  exact fin15Anchored_clause05221 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05222 chi hone hbad
                ·
                  exact fin15Anchored_clause05223 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05224 chi hone hbad
                ·
                  exact fin15Anchored_clause05225 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05226 chi hone hbad
                ·
                  exact fin15Anchored_clause05227 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05228 chi hone hbad
                ·
                  exact fin15Anchored_clause05229 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05230 chi hone hbad
                ·
                  exact fin15Anchored_clause05231 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05232 chi hone hbad
                ·
                  exact fin15Anchored_clause05233 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05234 chi hone hbad
                ·
                  exact fin15Anchored_clause05235 chi hone hbad
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
                exact fin15Anchored_clause05236 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05237 chi hone hbad
                ·
                  exact fin15Anchored_clause05238 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05239 chi hone hbad
                ·
                  exact fin15Anchored_clause05240 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05241 chi hone hbad
                ·
                  exact fin15Anchored_clause05242 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05243 chi hone hbad
                ·
                  exact fin15Anchored_clause05244 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05245 chi hone hbad
                ·
                  exact fin15Anchored_clause05246 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05247 chi hone hbad
                ·
                  exact fin15Anchored_clause05248 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05249 chi hone hbad
                ·
                  exact fin15Anchored_clause05250 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05251 chi hone hbad
                ·
                  exact fin15Anchored_clause05252 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05253 chi hone hbad
                ·
                  exact fin15Anchored_clause05254 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05255 chi hone hbad
                ·
                  exact fin15Anchored_clause05256 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05257 chi hone hbad
                ·
                  exact fin15Anchored_clause05258 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05259 chi hone hbad
                ·
                  exact fin15Anchored_clause05260 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05261 chi hone hbad
                ·
                  exact fin15Anchored_clause05262 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05263 chi hone hbad
                ·
                  exact fin15Anchored_clause05264 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05265 chi hone hbad
                ·
                  exact fin15Anchored_clause05266 chi hone hbad
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
                  exact fin15Anchored_clause05267 chi hone hbad
                ·
                  exact fin15Anchored_clause05268 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05269 chi hone hbad
                ·
                  exact fin15Anchored_clause05270 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05271 chi hone hbad
                ·
                  exact fin15Anchored_clause05272 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05273 chi hone hbad
                ·
                  exact fin15Anchored_clause05274 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05275 chi hone hbad
                ·
                  exact fin15Anchored_clause05276 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05277 chi hone hbad
                ·
                  exact fin15Anchored_clause05278 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05279 chi hone hbad
                ·
                  exact fin15Anchored_clause05280 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05281 chi hone hbad
                ·
                  exact fin15Anchored_clause05282 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05283 chi hone hbad
                ·
                  exact fin15Anchored_clause05284 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05285 chi hone hbad
                ·
                  exact fin15Anchored_clause05286 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05287 chi hone hbad
                ·
                  exact fin15Anchored_clause05288 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05289 chi hone hbad
                ·
                  exact fin15Anchored_clause05290 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05291 chi hone hbad
                ·
                  exact fin15Anchored_clause05292 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05293 chi hone hbad
                ·
                  exact fin15Anchored_clause05294 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05295 chi hone hbad
                ·
                  exact fin15Anchored_clause05296 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05297 chi hone hbad
                ·
                  exact fin15Anchored_clause05298 chi hone hbad

end ErdosSzekeres

end
