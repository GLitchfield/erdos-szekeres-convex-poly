module

public import ErdosSzekeres.Fin15AnchoredClauseChunk037
public import ErdosSzekeres.Fin15AnchoredClauseChunk038
public import ErdosSzekeres.Fin15AnchoredClauseChunk039

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 019. -/

theorem fin15Anchored_rejectSemanticSegment019
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      ((¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi))) ∨
      (((¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi)) ∨
      ((Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi)))) ∨
      ((((Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi)) ∨
      ((¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0453 chi))) ∨
      (((¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0453 chi)) ∨
      ((Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0453 chi))))) ∨
      (((((¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi)) ∨
      ((¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi))) ∨
      (((Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0454 chi)) ∨
      ((¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi)))) ∨
      ((((¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi)) ∨
      ((Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi))) ∨
      (((Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi)))) ∨
      ((((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi))))) ∨
      (((((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi)))) ∨
      ((((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi)))) ∨
      ((((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi))))) ∨
      (((((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi)))) ∨
      ((((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi))) ∨
      (((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi)))) ∨
      ((((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi))) ∨
      (((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi))))) ∨
      (((((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi))) ∨
      (((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi)))) ∨
      ((((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi))) ∨
      (((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi))) ∨
      (((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi)))) ∨
      ((((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi))) ∨
      (((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi))))) ∨
      (((((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi))) ∨
      (((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi)))) ∨
      ((((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi)) ∨
      ((¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi))) ∨
      (((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi)) ∨
      ((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi)) ∨
      ((¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi))) ∨
      (((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi)) ∨
      ((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi)))) ∨
      ((((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi)) ∨
      ((¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi))) ∨
      (((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi)) ∨
      ((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi))))) ∨
      (((((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi)) ∨
      ((¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi))) ∨
      (((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi)) ∨
      ((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi)))) ∨
      ((((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi)) ∨
      ((¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi))) ∨
      (((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi)) ∨
      ((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi))) ∨
      (((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi)) ∨
      ((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi)))) ∨
      ((((¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi))) ∨
      (((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi)) ∨
      ((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi))))) ∨
      (((((¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi))) ∨
      (((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi)) ∨
      ((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi)))) ∨
      ((((¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi))) ∨
      (((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi)) ∨
      ((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi))) ∨
      (((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi)) ∨
      ((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi)))) ∨
      ((((¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0362 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0362 chi)) ∨
      ((¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0362 chi))) ∨
      (((Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0362 chi)) ∨
      ((Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi))))) ∨
      (((((¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi)) ∨
      ((¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi))) ∨
      (((Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi)) ∨
      ((Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi)))) ∨
      ((((¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi)) ∨
      ((¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi))) ∨
      (((Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi)) ∨
      ((Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi)))))))))) := by
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
                exact fin15Anchored_clause04794 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04795 chi hone hbad
                ·
                  exact fin15Anchored_clause04796 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04797 chi hone hbad
                ·
                  exact fin15Anchored_clause04798 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04799 chi hone hbad
                ·
                  exact fin15Anchored_clause04800 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04801 chi hone hbad
                ·
                  exact fin15Anchored_clause04802 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04803 chi hone hbad
                ·
                  exact fin15Anchored_clause04804 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04805 chi hone hbad
                ·
                  exact fin15Anchored_clause04806 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04807 chi hone hbad
                ·
                  exact fin15Anchored_clause04808 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04809 chi hone hbad
                ·
                  exact fin15Anchored_clause04810 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04811 chi hone hbad
                ·
                  exact fin15Anchored_clause04812 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04813 chi hone hbad
                ·
                  exact fin15Anchored_clause04814 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04815 chi hone hbad
                ·
                  exact fin15Anchored_clause04816 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04817 chi hone hbad
                ·
                  exact fin15Anchored_clause04818 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04819 chi hone hbad
                ·
                  exact fin15Anchored_clause04820 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04821 chi hone hbad
                ·
                  exact fin15Anchored_clause04822 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04823 chi hone hbad
                ·
                  exact fin15Anchored_clause04824 chi hone hbad
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
                  exact fin15Anchored_clause04825 chi hone hbad
                ·
                  exact fin15Anchored_clause04826 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04827 chi hone hbad
                ·
                  exact fin15Anchored_clause04828 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04829 chi hone hbad
                ·
                  exact fin15Anchored_clause04830 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04831 chi hone hbad
                ·
                  exact fin15Anchored_clause04832 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04833 chi hone hbad
                ·
                  exact fin15Anchored_clause04834 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04835 chi hone hbad
                ·
                  exact fin15Anchored_clause04836 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04837 chi hone hbad
                ·
                  exact fin15Anchored_clause04838 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04839 chi hone hbad
                ·
                  exact fin15Anchored_clause04840 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04841 chi hone hbad
                ·
                  exact fin15Anchored_clause04842 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04843 chi hone hbad
                ·
                  exact fin15Anchored_clause04844 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04845 chi hone hbad
                ·
                  exact fin15Anchored_clause04846 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04847 chi hone hbad
                ·
                  exact fin15Anchored_clause04848 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04849 chi hone hbad
                ·
                  exact fin15Anchored_clause04850 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04851 chi hone hbad
                ·
                  exact fin15Anchored_clause04852 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04853 chi hone hbad
                ·
                  exact fin15Anchored_clause04854 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04855 chi hone hbad
                ·
                  exact fin15Anchored_clause04856 chi hone hbad
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
                exact fin15Anchored_clause04857 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04858 chi hone hbad
                ·
                  exact fin15Anchored_clause04859 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04860 chi hone hbad
                ·
                  exact fin15Anchored_clause04861 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04862 chi hone hbad
                ·
                  exact fin15Anchored_clause04863 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04864 chi hone hbad
                ·
                  exact fin15Anchored_clause04865 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04866 chi hone hbad
                ·
                  exact fin15Anchored_clause04867 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04868 chi hone hbad
                ·
                  exact fin15Anchored_clause04869 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04870 chi hone hbad
                ·
                  exact fin15Anchored_clause04871 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04872 chi hone hbad
                ·
                  exact fin15Anchored_clause04873 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04874 chi hone hbad
                ·
                  exact fin15Anchored_clause04875 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04876 chi hone hbad
                ·
                  exact fin15Anchored_clause04877 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04878 chi hone hbad
                ·
                  exact fin15Anchored_clause04879 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04880 chi hone hbad
                ·
                  exact fin15Anchored_clause04881 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04882 chi hone hbad
                ·
                  exact fin15Anchored_clause04883 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04884 chi hone hbad
                ·
                  exact fin15Anchored_clause04885 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04886 chi hone hbad
                ·
                  exact fin15Anchored_clause04887 chi hone hbad
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
                  exact fin15Anchored_clause04888 chi hone hbad
                ·
                  exact fin15Anchored_clause04889 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04890 chi hone hbad
                ·
                  exact fin15Anchored_clause04891 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04892 chi hone hbad
                ·
                  exact fin15Anchored_clause04893 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04894 chi hone hbad
                ·
                  exact fin15Anchored_clause04895 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04896 chi hone hbad
                ·
                  exact fin15Anchored_clause04897 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04898 chi hone hbad
                ·
                  exact fin15Anchored_clause04899 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04900 chi hone hbad
                ·
                  exact fin15Anchored_clause04901 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04902 chi hone hbad
                ·
                  exact fin15Anchored_clause04903 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04904 chi hone hbad
                ·
                  exact fin15Anchored_clause04905 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04906 chi hone hbad
                ·
                  exact fin15Anchored_clause04907 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04908 chi hone hbad
                ·
                  exact fin15Anchored_clause04909 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04910 chi hone hbad
                ·
                  exact fin15Anchored_clause04911 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04912 chi hone hbad
                ·
                  exact fin15Anchored_clause04913 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04914 chi hone hbad
                ·
                  exact fin15Anchored_clause04915 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04916 chi hone hbad
                ·
                  exact fin15Anchored_clause04917 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04918 chi hone hbad
                ·
                  exact fin15Anchored_clause04919 chi hone hbad
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
                exact fin15Anchored_clause04920 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04921 chi hone hbad
                ·
                  exact fin15Anchored_clause04922 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04923 chi hone hbad
                ·
                  exact fin15Anchored_clause04924 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04925 chi hone hbad
                ·
                  exact fin15Anchored_clause04926 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04927 chi hone hbad
                ·
                  exact fin15Anchored_clause04928 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04929 chi hone hbad
                ·
                  exact fin15Anchored_clause04930 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04931 chi hone hbad
                ·
                  exact fin15Anchored_clause04932 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04933 chi hone hbad
                ·
                  exact fin15Anchored_clause04934 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04935 chi hone hbad
                ·
                  exact fin15Anchored_clause04936 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04937 chi hone hbad
                ·
                  exact fin15Anchored_clause04938 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04939 chi hone hbad
                ·
                  exact fin15Anchored_clause04940 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04941 chi hone hbad
                ·
                  exact fin15Anchored_clause04942 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04943 chi hone hbad
                ·
                  exact fin15Anchored_clause04944 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04945 chi hone hbad
                ·
                  exact fin15Anchored_clause04946 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04947 chi hone hbad
                ·
                  exact fin15Anchored_clause04948 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04949 chi hone hbad
                ·
                  exact fin15Anchored_clause04950 chi hone hbad
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
                  exact fin15Anchored_clause04951 chi hone hbad
                ·
                  exact fin15Anchored_clause04952 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04953 chi hone hbad
                ·
                  exact fin15Anchored_clause04954 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04955 chi hone hbad
                ·
                  exact fin15Anchored_clause04956 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04957 chi hone hbad
                ·
                  exact fin15Anchored_clause04958 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04959 chi hone hbad
                ·
                  exact fin15Anchored_clause04960 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04961 chi hone hbad
                ·
                  exact fin15Anchored_clause04962 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04963 chi hone hbad
                ·
                  exact fin15Anchored_clause04964 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04965 chi hone hbad
                ·
                  exact fin15Anchored_clause04966 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04967 chi hone hbad
                ·
                  exact fin15Anchored_clause04968 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04969 chi hone hbad
                ·
                  exact fin15Anchored_clause04970 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04971 chi hone hbad
                ·
                  exact fin15Anchored_clause04972 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04973 chi hone hbad
                ·
                  exact fin15Anchored_clause04974 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04975 chi hone hbad
                ·
                  exact fin15Anchored_clause04976 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04977 chi hone hbad
                ·
                  exact fin15Anchored_clause04978 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04979 chi hone hbad
                ·
                  exact fin15Anchored_clause04980 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04981 chi hone hbad
                ·
                  exact fin15Anchored_clause04982 chi hone hbad
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
                  exact fin15Anchored_clause04983 chi hone hbad
                ·
                  exact fin15Anchored_clause04984 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04985 chi hone hbad
                ·
                  exact fin15Anchored_clause04986 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04987 chi hone hbad
                ·
                  exact fin15Anchored_clause04988 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04989 chi hone hbad
                ·
                  exact fin15Anchored_clause04990 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04991 chi hone hbad
                ·
                  exact fin15Anchored_clause04992 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04993 chi hone hbad
                ·
                  exact fin15Anchored_clause04994 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04995 chi hone hbad
                ·
                  exact fin15Anchored_clause04996 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04997 chi hone hbad
                ·
                  exact fin15Anchored_clause04998 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause04999 chi hone hbad
                ·
                  exact fin15Anchored_clause05000 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05001 chi hone hbad
                ·
                  exact fin15Anchored_clause05002 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05003 chi hone hbad
                ·
                  exact fin15Anchored_clause05004 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05005 chi hone hbad
                ·
                  exact fin15Anchored_clause05006 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05007 chi hone hbad
                ·
                  exact fin15Anchored_clause05008 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05009 chi hone hbad
                ·
                  exact fin15Anchored_clause05010 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05011 chi hone hbad
                ·
                  exact fin15Anchored_clause05012 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05013 chi hone hbad
                ·
                  exact fin15Anchored_clause05014 chi hone hbad
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
                  exact fin15Anchored_clause05015 chi hone hbad
                ·
                  exact fin15Anchored_clause05016 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05017 chi hone hbad
                ·
                  exact fin15Anchored_clause05018 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05019 chi hone hbad
                ·
                  exact fin15Anchored_clause05020 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05021 chi hone hbad
                ·
                  exact fin15Anchored_clause05022 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05023 chi hone hbad
                ·
                  exact fin15Anchored_clause05024 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05025 chi hone hbad
                ·
                  exact fin15Anchored_clause05026 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05027 chi hone hbad
                ·
                  exact fin15Anchored_clause05028 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05029 chi hone hbad
                ·
                  exact fin15Anchored_clause05030 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05031 chi hone hbad
                ·
                  exact fin15Anchored_clause05032 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05033 chi hone hbad
                ·
                  exact fin15Anchored_clause05034 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05035 chi hone hbad
                ·
                  exact fin15Anchored_clause05036 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05037 chi hone hbad
                ·
                  exact fin15Anchored_clause05038 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05039 chi hone hbad
                ·
                  exact fin15Anchored_clause05040 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05041 chi hone hbad
                ·
                  exact fin15Anchored_clause05042 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05043 chi hone hbad
                ·
                  exact fin15Anchored_clause05044 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05045 chi hone hbad
                ·
                  exact fin15Anchored_clause05046 chi hone hbad

end ErdosSzekeres

end
