module

public import ErdosSzekeres.Fin15AnchoredClauseChunk045
public import ErdosSzekeres.Fin15AnchoredClauseChunk046
public import ErdosSzekeres.Fin15AnchoredClauseChunk047

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 023. -/

theorem fin15Anchored_rejectSemanticSegment023
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi))) ∨
      (((Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi)) ∨
      ((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi)))) ∨
      ((((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi)) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi))) ∨
      (((Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi)) ∨
      ((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi))))) ∨
      (((((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi)) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi))) ∨
      (((Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi)) ∨
      ((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi)))) ∨
      ((((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi)) ∨
      ((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi))) ∨
      (((Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi)) ∨
      ((Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi)) ∨
      ((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi))) ∨
      (((Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi)) ∨
      ((Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi)))) ∨
      ((((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi)) ∨
      ((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi))) ∨
      (((Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi)) ∨
      ((Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi))))) ∨
      (((((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      (¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi)) ∨
      ((¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi))) ∨
      (((Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi) ∨
      (Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi)) ∨
      ((Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi) ∨
      (¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0394 chi)))) ∨
      ((((¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0394 chi) ∨
      (¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi)) ∨
      ((¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0394 chi) ∨
      (Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi))) ∨
      (((Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi) ∨
      (Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi)) ∨
      ((¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0395 chi) ∨
      (¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0395 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0395 chi) ∨
      ((¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0395 chi) ∨
      (Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0395 chi))) ∨
      (((Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0395 chi) ∨
      (Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0395 chi)) ∨
      ((Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0395 chi) ∨
      (¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0396 chi)))) ∨
      ((((¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0396 chi) ∨
      (¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0396 chi)) ∨
      ((¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi) ∨
      (¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi))) ∨
      (((¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi)) ∨
      ((Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi))))) ∨
      (((((Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi) ∨
      (Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi)) ∨
      ((¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi) ∨
      (¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi))) ∨
      (((¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi)) ∨
      ((Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi)))) ∨
      ((((Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi) ∨
      (Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi)) ∨
      ((¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi) ∨
      (¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi))) ∨
      (((¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi) ∨
      (¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi)) ∨
      ((Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi) ∨
      (Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi)))))) ∨
      ((((((Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi) ∨
      (Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi)) ∨
      ((¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi))) ∨
      (((¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi)) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi)))) ∨
      ((((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi)) ∨
      ((¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi))) ∨
      (((¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi)) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi))))) ∨
      (((((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi)) ∨
      ((¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi))) ∨
      (((¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi)) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi)))) ∨
      ((((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi)) ∨
      ((¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi))) ∨
      (((¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi)) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi))) ∨
      (((¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi)) ∨
      ((¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi)))) ∨
      ((((Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi)) ∨
      ((Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi))) ∨
      (((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi)) ∨
      ((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi))))) ∨
      (((((Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi)) ∨
      ((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi))) ∨
      (((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi)) ∨
      ((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi)))) ∨
      ((((Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi)) ∨
      ((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi))) ∨
      (((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi)) ∨
      ((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi)))))) ∨
      ((((((Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi)) ∨
      ((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi))) ∨
      (((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi)) ∨
      ((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi)))) ∨
      ((((Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi)) ∨
      ((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi))) ∨
      (((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi)) ∨
      ((¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi))))) ∨
      (((((Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi)) ∨
      ((Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi))) ∨
      (((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi)) ∨
      ((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi)))) ∨
      ((((Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi)) ∨
      ((Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi))) ∨
      (((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi)) ∨
      ((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi))))))) ∨
      (((((((Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi)) ∨
      ((Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi))) ∨
      (((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi)) ∨
      ((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi)))) ∨
      ((((Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi)) ∨
      ((Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0413 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi))) ∨
      (((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi) ∨
      (¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi)) ∨
      ((¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi))))) ∨
      (((((Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi)) ∨
      ((Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi) ∨
      (¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi))) ∨
      (((¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi) ∨
      (¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi)) ∨
      ((¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi) ∨
      (Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi)))) ∨
      ((((Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi) ∨
      (Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi)) ∨
      ((Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi) ∨
      (¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0416 chi))) ∨
      (((¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0416 chi) ∨
      (¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0416 chi)) ∨
      ((¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0417 chi) ∨
      (Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0417 chi)))))) ∨
      ((((((Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0417 chi) ∨
      (Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0417 chi)) ∨
      ((¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi) ∨
      (¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi))) ∨
      (((¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi)) ∨
      ((Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi)))) ∨
      ((((Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi)) ∨
      ((¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi) ∨
      (¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi))) ∨
      (((¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi)) ∨
      ((Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi))))) ∨
      (((((Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi)) ∨
      ((¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi) ∨
      (¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi))) ∨
      (((¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      (¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi)) ∨
      ((Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      (Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi)))) ∨
      ((((Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      (Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi)) ∨
      ((¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi))) ∨
      (((¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi)) ∨
      ((Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi)))))))))) := by
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
                exact fin15Anchored_clause05804 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05805 chi hone hbad
                ·
                  exact fin15Anchored_clause05806 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05807 chi hone hbad
                ·
                  exact fin15Anchored_clause05808 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05809 chi hone hbad
                ·
                  exact fin15Anchored_clause05810 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05811 chi hone hbad
                ·
                  exact fin15Anchored_clause05812 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05813 chi hone hbad
                ·
                  exact fin15Anchored_clause05814 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05815 chi hone hbad
                ·
                  exact fin15Anchored_clause05816 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05817 chi hone hbad
                ·
                  exact fin15Anchored_clause05818 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05819 chi hone hbad
                ·
                  exact fin15Anchored_clause05820 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05821 chi hone hbad
                ·
                  exact fin15Anchored_clause05822 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05823 chi hone hbad
                ·
                  exact fin15Anchored_clause05824 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05825 chi hone hbad
                ·
                  exact fin15Anchored_clause05826 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05827 chi hone hbad
                ·
                  exact fin15Anchored_clause05828 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05829 chi hone hbad
                ·
                  exact fin15Anchored_clause05830 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05831 chi hone hbad
                ·
                  exact fin15Anchored_clause05832 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05833 chi hone hbad
                ·
                  exact fin15Anchored_clause05834 chi hone hbad
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
                  exact fin15Anchored_clause05835 chi hone hbad
                ·
                  exact fin15Anchored_clause05836 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05837 chi hone hbad
                ·
                  exact fin15Anchored_clause05838 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05839 chi hone hbad
                ·
                  exact fin15Anchored_clause05840 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05841 chi hone hbad
                ·
                  exact fin15Anchored_clause05842 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05843 chi hone hbad
                ·
                  exact fin15Anchored_clause05844 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05845 chi hone hbad
                ·
                  exact fin15Anchored_clause05846 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05847 chi hone hbad
                ·
                  exact fin15Anchored_clause05848 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05849 chi hone hbad
                ·
                  exact fin15Anchored_clause05850 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05851 chi hone hbad
                ·
                  exact fin15Anchored_clause05852 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05853 chi hone hbad
                ·
                  exact fin15Anchored_clause05854 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05855 chi hone hbad
                ·
                  exact fin15Anchored_clause05856 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05857 chi hone hbad
                ·
                  exact fin15Anchored_clause05858 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05859 chi hone hbad
                ·
                  exact fin15Anchored_clause05860 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05861 chi hone hbad
                ·
                  exact fin15Anchored_clause05862 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05863 chi hone hbad
                ·
                  exact fin15Anchored_clause05864 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05865 chi hone hbad
                ·
                  exact fin15Anchored_clause05866 chi hone hbad
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
                exact fin15Anchored_clause05867 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05868 chi hone hbad
                ·
                  exact fin15Anchored_clause05869 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05870 chi hone hbad
                ·
                  exact fin15Anchored_clause05871 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05872 chi hone hbad
                ·
                  exact fin15Anchored_clause05873 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05874 chi hone hbad
                ·
                  exact fin15Anchored_clause05875 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05876 chi hone hbad
                ·
                  exact fin15Anchored_clause05877 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05878 chi hone hbad
                ·
                  exact fin15Anchored_clause05879 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05880 chi hone hbad
                ·
                  exact fin15Anchored_clause05881 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05882 chi hone hbad
                ·
                  exact fin15Anchored_clause05883 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05884 chi hone hbad
                ·
                  exact fin15Anchored_clause05885 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05886 chi hone hbad
                ·
                  exact fin15Anchored_clause05887 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05888 chi hone hbad
                ·
                  exact fin15Anchored_clause05889 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05890 chi hone hbad
                ·
                  exact fin15Anchored_clause05891 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05892 chi hone hbad
                ·
                  exact fin15Anchored_clause05893 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05894 chi hone hbad
                ·
                  exact fin15Anchored_clause05895 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05896 chi hone hbad
                ·
                  exact fin15Anchored_clause05897 chi hone hbad
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
                  exact fin15Anchored_clause05898 chi hone hbad
                ·
                  exact fin15Anchored_clause05899 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05900 chi hone hbad
                ·
                  exact fin15Anchored_clause05901 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05902 chi hone hbad
                ·
                  exact fin15Anchored_clause05903 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05904 chi hone hbad
                ·
                  exact fin15Anchored_clause05905 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05906 chi hone hbad
                ·
                  exact fin15Anchored_clause05907 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05908 chi hone hbad
                ·
                  exact fin15Anchored_clause05909 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05910 chi hone hbad
                ·
                  exact fin15Anchored_clause05911 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05912 chi hone hbad
                ·
                  exact fin15Anchored_clause05913 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05914 chi hone hbad
                ·
                  exact fin15Anchored_clause05915 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05916 chi hone hbad
                ·
                  exact fin15Anchored_clause05917 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05918 chi hone hbad
                ·
                  exact fin15Anchored_clause05919 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05920 chi hone hbad
                ·
                  exact fin15Anchored_clause05921 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05922 chi hone hbad
                ·
                  exact fin15Anchored_clause05923 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05924 chi hone hbad
                ·
                  exact fin15Anchored_clause05925 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05926 chi hone hbad
                ·
                  exact fin15Anchored_clause05927 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05928 chi hone hbad
                ·
                  exact fin15Anchored_clause05929 chi hone hbad
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
                exact fin15Anchored_clause05930 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05931 chi hone hbad
                ·
                  exact fin15Anchored_clause05932 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05933 chi hone hbad
                ·
                  exact fin15Anchored_clause05934 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05935 chi hone hbad
                ·
                  exact fin15Anchored_clause05936 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05937 chi hone hbad
                ·
                  exact fin15Anchored_clause05938 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05939 chi hone hbad
                ·
                  exact fin15Anchored_clause05940 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05941 chi hone hbad
                ·
                  exact fin15Anchored_clause05942 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05943 chi hone hbad
                ·
                  exact fin15Anchored_clause05944 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05945 chi hone hbad
                ·
                  exact fin15Anchored_clause05946 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05947 chi hone hbad
                ·
                  exact fin15Anchored_clause05948 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05949 chi hone hbad
                ·
                  exact fin15Anchored_clause05950 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05951 chi hone hbad
                ·
                  exact fin15Anchored_clause05952 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05953 chi hone hbad
                ·
                  exact fin15Anchored_clause05954 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05955 chi hone hbad
                ·
                  exact fin15Anchored_clause05956 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05957 chi hone hbad
                ·
                  exact fin15Anchored_clause05958 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05959 chi hone hbad
                ·
                  exact fin15Anchored_clause05960 chi hone hbad
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
                  exact fin15Anchored_clause05961 chi hone hbad
                ·
                  exact fin15Anchored_clause05962 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05963 chi hone hbad
                ·
                  exact fin15Anchored_clause05964 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05965 chi hone hbad
                ·
                  exact fin15Anchored_clause05966 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05967 chi hone hbad
                ·
                  exact fin15Anchored_clause05968 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05969 chi hone hbad
                ·
                  exact fin15Anchored_clause05970 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05971 chi hone hbad
                ·
                  exact fin15Anchored_clause05972 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05973 chi hone hbad
                ·
                  exact fin15Anchored_clause05974 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05975 chi hone hbad
                ·
                  exact fin15Anchored_clause05976 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05977 chi hone hbad
                ·
                  exact fin15Anchored_clause05978 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05979 chi hone hbad
                ·
                  exact fin15Anchored_clause05980 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05981 chi hone hbad
                ·
                  exact fin15Anchored_clause05982 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05983 chi hone hbad
                ·
                  exact fin15Anchored_clause05984 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05985 chi hone hbad
                ·
                  exact fin15Anchored_clause05986 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05987 chi hone hbad
                ·
                  exact fin15Anchored_clause05988 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05989 chi hone hbad
                ·
                  exact fin15Anchored_clause05990 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05991 chi hone hbad
                ·
                  exact fin15Anchored_clause05992 chi hone hbad
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
                  exact fin15Anchored_clause05993 chi hone hbad
                ·
                  exact fin15Anchored_clause05994 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05995 chi hone hbad
                ·
                  exact fin15Anchored_clause05996 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05997 chi hone hbad
                ·
                  exact fin15Anchored_clause05998 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05999 chi hone hbad
                ·
                  exact fin15Anchored_clause06000 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06001 chi hone hbad
                ·
                  exact fin15Anchored_clause06002 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06003 chi hone hbad
                ·
                  exact fin15Anchored_clause06004 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06005 chi hone hbad
                ·
                  exact fin15Anchored_clause06006 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06007 chi hone hbad
                ·
                  exact fin15Anchored_clause06008 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06009 chi hone hbad
                ·
                  exact fin15Anchored_clause06010 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06011 chi hone hbad
                ·
                  exact fin15Anchored_clause06012 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06013 chi hone hbad
                ·
                  exact fin15Anchored_clause06014 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06015 chi hone hbad
                ·
                  exact fin15Anchored_clause06016 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06017 chi hone hbad
                ·
                  exact fin15Anchored_clause06018 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06019 chi hone hbad
                ·
                  exact fin15Anchored_clause06020 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06021 chi hone hbad
                ·
                  exact fin15Anchored_clause06022 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06023 chi hone hbad
                ·
                  exact fin15Anchored_clause06024 chi hone hbad
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
                  exact fin15Anchored_clause06025 chi hone hbad
                ·
                  exact fin15Anchored_clause06026 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06027 chi hone hbad
                ·
                  exact fin15Anchored_clause06028 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06029 chi hone hbad
                ·
                  exact fin15Anchored_clause06030 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06031 chi hone hbad
                ·
                  exact fin15Anchored_clause06032 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06033 chi hone hbad
                ·
                  exact fin15Anchored_clause06034 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06035 chi hone hbad
                ·
                  exact fin15Anchored_clause06036 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06037 chi hone hbad
                ·
                  exact fin15Anchored_clause06038 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06039 chi hone hbad
                ·
                  exact fin15Anchored_clause06040 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06041 chi hone hbad
                ·
                  exact fin15Anchored_clause06042 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06043 chi hone hbad
                ·
                  exact fin15Anchored_clause06044 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06045 chi hone hbad
                ·
                  exact fin15Anchored_clause06046 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06047 chi hone hbad
                ·
                  exact fin15Anchored_clause06048 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06049 chi hone hbad
                ·
                  exact fin15Anchored_clause06050 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06051 chi hone hbad
                ·
                  exact fin15Anchored_clause06052 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06053 chi hone hbad
                ·
                  exact fin15Anchored_clause06054 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06055 chi hone hbad
                ·
                  exact fin15Anchored_clause06056 chi hone hbad

end ErdosSzekeres

end
