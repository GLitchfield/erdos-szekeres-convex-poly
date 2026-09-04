module

public import ErdosSzekeres.Fin15AnchoredClauseChunk049
public import ErdosSzekeres.Fin15AnchoredClauseChunk050
public import ErdosSzekeres.Fin15AnchoredClauseChunk051

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 025. -/

theorem fin15Anchored_rejectSemanticSegment025
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi))) ∨
      (((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi)) ∨
      ((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi)))) ∨
      ((((¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi))) ∨
      (((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi)) ∨
      ((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi))))) ∨
      (((((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi))) ∨
      (((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi)) ∨
      ((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi)))) ∨
      ((((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi))) ∨
      (((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi)) ∨
      ((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi))) ∨
      (((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi)) ∨
      ((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi)))) ∨
      ((((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi))) ∨
      (((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi)) ∨
      ((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi))))) ∨
      (((((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi))) ∨
      (((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi)) ∨
      ((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi)))) ∨
      ((((¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi)) ∨
      ((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi))) ∨
      (((Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi)) ∨
      ((Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      ((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi))) ∨
      (((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi)) ∨
      ((Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi)))) ∨
      ((((Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi)) ∨
      ((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi))) ∨
      (((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi)) ∨
      ((Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi))))) ∨
      (((((Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi)) ∨
      ((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi))) ∨
      (((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi)) ∨
      ((Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi)))) ∨
      ((((Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi)) ∨
      ((¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0415 chi))) ∨
      (((¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi) ∨
      (Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0415 chi)) ∨
      ((Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi) ∨
      (Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0415 chi)))))) ∨
      ((((((Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0415 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi)) ∨
      ((¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi))) ∨
      (((Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0416 chi) ∨
      (Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi)) ∨
      ((Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0416 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi)))) ∨
      ((((¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi)) ∨
      ((Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi) ∨
      (Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi))) ∨
      (((Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi) ∨
      (Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi)) ∨
      ((¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi) ∨
      (¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi))))) ∨
      (((((¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi)) ∨
      ((Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi))) ∨
      (((Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi) ∨
      (Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi)) ∨
      ((¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi) ∨
      (¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi)))) ∨
      ((((¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi)) ∨
      ((Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi))) ∨
      (((Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi) ∨
      (Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi)) ∨
      ((¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi) ∨
      (¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      ((¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi) ∨
      (Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi))) ∨
      (((Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi) ∨
      (Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi)) ∨
      ((Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0420 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi)))) ∨
      ((((¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi)) ∨
      ((¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi))) ∨
      (((Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi)) ∨
      ((Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi))))) ∨
      (((((¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi)) ∨
      ((¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi))) ∨
      (((Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi)) ∨
      ((Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi)))) ∨
      ((((¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi)) ∨
      ((¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi))) ∨
      (((Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0424 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi)) ∨
      ((Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0424 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi) ∨
      (¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi)) ∨
      ((¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi))) ∨
      (((Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0425 chi) ∨
      (Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi)) ∨
      ((Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0425 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi)))) ∨
      ((((¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi)) ∨
      ((¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi))) ∨
      (((Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi)) ∨
      ((Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0427 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi))))) ∨
      (((((¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi)) ∨
      ((¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi))) ∨
      (((Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi)) ∨
      ((Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0428 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi)))) ∨
      ((((¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi)) ∨
      ((¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi))) ∨
      (((Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi)) ∨
      ((Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0429 chi) ∨
      (¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi)) ∨
      ((¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi))) ∨
      (((Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi)) ∨
      ((Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi)))) ∨
      ((((¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi)) ∨
      ((¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi))) ∨
      (((Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi)) ∨
      ((Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0434 chi) ∨
      (¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi))))) ∨
      (((((¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi)) ∨
      ((¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi))) ∨
      (((Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi)) ∨
      ((Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi)))) ∨
      ((((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi)) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi))) ∨
      (((Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi)) ∨
      ((Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi)) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi))) ∨
      (((Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi)) ∨
      ((Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi)))) ∨
      ((((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi)) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi))) ∨
      (((Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi)) ∨
      ((Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi))))) ∨
      (((((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi)) ∨
      ((¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi))) ∨
      (((Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi)) ∨
      ((Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi)))) ∨
      ((((¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi)) ∨
      ((¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi))) ∨
      (((Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi)) ∨
      ((Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi)))))))))) := by
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
                exact fin15Anchored_clause06309 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06310 chi hone hbad
                ·
                  exact fin15Anchored_clause06311 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06312 chi hone hbad
                ·
                  exact fin15Anchored_clause06313 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06314 chi hone hbad
                ·
                  exact fin15Anchored_clause06315 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06316 chi hone hbad
                ·
                  exact fin15Anchored_clause06317 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06318 chi hone hbad
                ·
                  exact fin15Anchored_clause06319 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06320 chi hone hbad
                ·
                  exact fin15Anchored_clause06321 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06322 chi hone hbad
                ·
                  exact fin15Anchored_clause06323 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06324 chi hone hbad
                ·
                  exact fin15Anchored_clause06325 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06326 chi hone hbad
                ·
                  exact fin15Anchored_clause06327 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06328 chi hone hbad
                ·
                  exact fin15Anchored_clause06329 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06330 chi hone hbad
                ·
                  exact fin15Anchored_clause06331 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06332 chi hone hbad
                ·
                  exact fin15Anchored_clause06333 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06334 chi hone hbad
                ·
                  exact fin15Anchored_clause06335 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06336 chi hone hbad
                ·
                  exact fin15Anchored_clause06337 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06338 chi hone hbad
                ·
                  exact fin15Anchored_clause06339 chi hone hbad
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
                  exact fin15Anchored_clause06340 chi hone hbad
                ·
                  exact fin15Anchored_clause06341 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06342 chi hone hbad
                ·
                  exact fin15Anchored_clause06343 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06344 chi hone hbad
                ·
                  exact fin15Anchored_clause06345 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06346 chi hone hbad
                ·
                  exact fin15Anchored_clause06347 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06348 chi hone hbad
                ·
                  exact fin15Anchored_clause06349 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06350 chi hone hbad
                ·
                  exact fin15Anchored_clause06351 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06352 chi hone hbad
                ·
                  exact fin15Anchored_clause06353 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06354 chi hone hbad
                ·
                  exact fin15Anchored_clause06355 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06356 chi hone hbad
                ·
                  exact fin15Anchored_clause06357 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06358 chi hone hbad
                ·
                  exact fin15Anchored_clause06359 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06360 chi hone hbad
                ·
                  exact fin15Anchored_clause06361 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06362 chi hone hbad
                ·
                  exact fin15Anchored_clause06363 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06364 chi hone hbad
                ·
                  exact fin15Anchored_clause06365 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06366 chi hone hbad
                ·
                  exact fin15Anchored_clause06367 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06368 chi hone hbad
                ·
                  exact fin15Anchored_clause06369 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06370 chi hone hbad
                ·
                  exact fin15Anchored_clause06371 chi hone hbad
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
                exact fin15Anchored_clause06372 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06373 chi hone hbad
                ·
                  exact fin15Anchored_clause06374 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06375 chi hone hbad
                ·
                  exact fin15Anchored_clause06376 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06377 chi hone hbad
                ·
                  exact fin15Anchored_clause06378 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06379 chi hone hbad
                ·
                  exact fin15Anchored_clause06380 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06381 chi hone hbad
                ·
                  exact fin15Anchored_clause06382 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06383 chi hone hbad
                ·
                  exact fin15Anchored_clause06384 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06385 chi hone hbad
                ·
                  exact fin15Anchored_clause06386 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06387 chi hone hbad
                ·
                  exact fin15Anchored_clause06388 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06389 chi hone hbad
                ·
                  exact fin15Anchored_clause06390 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06391 chi hone hbad
                ·
                  exact fin15Anchored_clause06392 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06393 chi hone hbad
                ·
                  exact fin15Anchored_clause06394 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06395 chi hone hbad
                ·
                  exact fin15Anchored_clause06396 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06397 chi hone hbad
                ·
                  exact fin15Anchored_clause06398 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06399 chi hone hbad
                ·
                  exact fin15Anchored_clause06400 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06401 chi hone hbad
                ·
                  exact fin15Anchored_clause06402 chi hone hbad
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
                  exact fin15Anchored_clause06403 chi hone hbad
                ·
                  exact fin15Anchored_clause06404 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06405 chi hone hbad
                ·
                  exact fin15Anchored_clause06406 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06407 chi hone hbad
                ·
                  exact fin15Anchored_clause06408 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06409 chi hone hbad
                ·
                  exact fin15Anchored_clause06410 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06411 chi hone hbad
                ·
                  exact fin15Anchored_clause06412 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06413 chi hone hbad
                ·
                  exact fin15Anchored_clause06414 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06415 chi hone hbad
                ·
                  exact fin15Anchored_clause06416 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06417 chi hone hbad
                ·
                  exact fin15Anchored_clause06418 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06419 chi hone hbad
                ·
                  exact fin15Anchored_clause06420 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06421 chi hone hbad
                ·
                  exact fin15Anchored_clause06422 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06423 chi hone hbad
                ·
                  exact fin15Anchored_clause06424 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06425 chi hone hbad
                ·
                  exact fin15Anchored_clause06426 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06427 chi hone hbad
                ·
                  exact fin15Anchored_clause06428 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06429 chi hone hbad
                ·
                  exact fin15Anchored_clause06430 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06431 chi hone hbad
                ·
                  exact fin15Anchored_clause06432 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06433 chi hone hbad
                ·
                  exact fin15Anchored_clause06434 chi hone hbad
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
                exact fin15Anchored_clause06435 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06436 chi hone hbad
                ·
                  exact fin15Anchored_clause06437 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06438 chi hone hbad
                ·
                  exact fin15Anchored_clause06439 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06440 chi hone hbad
                ·
                  exact fin15Anchored_clause06441 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06442 chi hone hbad
                ·
                  exact fin15Anchored_clause06443 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06444 chi hone hbad
                ·
                  exact fin15Anchored_clause06445 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06446 chi hone hbad
                ·
                  exact fin15Anchored_clause06447 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06448 chi hone hbad
                ·
                  exact fin15Anchored_clause06449 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06450 chi hone hbad
                ·
                  exact fin15Anchored_clause06451 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06452 chi hone hbad
                ·
                  exact fin15Anchored_clause06453 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06454 chi hone hbad
                ·
                  exact fin15Anchored_clause06455 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06456 chi hone hbad
                ·
                  exact fin15Anchored_clause06457 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06458 chi hone hbad
                ·
                  exact fin15Anchored_clause06459 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06460 chi hone hbad
                ·
                  exact fin15Anchored_clause06461 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06462 chi hone hbad
                ·
                  exact fin15Anchored_clause06463 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06464 chi hone hbad
                ·
                  exact fin15Anchored_clause06465 chi hone hbad
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
                  exact fin15Anchored_clause06466 chi hone hbad
                ·
                  exact fin15Anchored_clause06467 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06468 chi hone hbad
                ·
                  exact fin15Anchored_clause06469 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06470 chi hone hbad
                ·
                  exact fin15Anchored_clause06471 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06472 chi hone hbad
                ·
                  exact fin15Anchored_clause06473 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06474 chi hone hbad
                ·
                  exact fin15Anchored_clause06475 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06476 chi hone hbad
                ·
                  exact fin15Anchored_clause06477 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06478 chi hone hbad
                ·
                  exact fin15Anchored_clause06479 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06480 chi hone hbad
                ·
                  exact fin15Anchored_clause06481 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06482 chi hone hbad
                ·
                  exact fin15Anchored_clause06483 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06484 chi hone hbad
                ·
                  exact fin15Anchored_clause06485 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06486 chi hone hbad
                ·
                  exact fin15Anchored_clause06487 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06488 chi hone hbad
                ·
                  exact fin15Anchored_clause06489 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06490 chi hone hbad
                ·
                  exact fin15Anchored_clause06491 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06492 chi hone hbad
                ·
                  exact fin15Anchored_clause06493 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06494 chi hone hbad
                ·
                  exact fin15Anchored_clause06495 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06496 chi hone hbad
                ·
                  exact fin15Anchored_clause06497 chi hone hbad
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
                  exact fin15Anchored_clause06498 chi hone hbad
                ·
                  exact fin15Anchored_clause06499 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06500 chi hone hbad
                ·
                  exact fin15Anchored_clause06501 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06502 chi hone hbad
                ·
                  exact fin15Anchored_clause06503 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06504 chi hone hbad
                ·
                  exact fin15Anchored_clause06505 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06506 chi hone hbad
                ·
                  exact fin15Anchored_clause06507 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06508 chi hone hbad
                ·
                  exact fin15Anchored_clause06509 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06510 chi hone hbad
                ·
                  exact fin15Anchored_clause06511 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06512 chi hone hbad
                ·
                  exact fin15Anchored_clause06513 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06514 chi hone hbad
                ·
                  exact fin15Anchored_clause06515 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06516 chi hone hbad
                ·
                  exact fin15Anchored_clause06517 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06518 chi hone hbad
                ·
                  exact fin15Anchored_clause06519 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06520 chi hone hbad
                ·
                  exact fin15Anchored_clause06521 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06522 chi hone hbad
                ·
                  exact fin15Anchored_clause06523 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06524 chi hone hbad
                ·
                  exact fin15Anchored_clause06525 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06526 chi hone hbad
                ·
                  exact fin15Anchored_clause06527 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06528 chi hone hbad
                ·
                  exact fin15Anchored_clause06529 chi hone hbad
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
                  exact fin15Anchored_clause06530 chi hone hbad
                ·
                  exact fin15Anchored_clause06531 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06532 chi hone hbad
                ·
                  exact fin15Anchored_clause06533 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06534 chi hone hbad
                ·
                  exact fin15Anchored_clause06535 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06536 chi hone hbad
                ·
                  exact fin15Anchored_clause06537 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06538 chi hone hbad
                ·
                  exact fin15Anchored_clause06539 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06540 chi hone hbad
                ·
                  exact fin15Anchored_clause06541 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06542 chi hone hbad
                ·
                  exact fin15Anchored_clause06543 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06544 chi hone hbad
                ·
                  exact fin15Anchored_clause06545 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06546 chi hone hbad
                ·
                  exact fin15Anchored_clause06547 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06548 chi hone hbad
                ·
                  exact fin15Anchored_clause06549 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06550 chi hone hbad
                ·
                  exact fin15Anchored_clause06551 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06552 chi hone hbad
                ·
                  exact fin15Anchored_clause06553 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06554 chi hone hbad
                ·
                  exact fin15Anchored_clause06555 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06556 chi hone hbad
                ·
                  exact fin15Anchored_clause06557 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06558 chi hone hbad
                ·
                  exact fin15Anchored_clause06559 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06560 chi hone hbad
                ·
                  exact fin15Anchored_clause06561 chi hone hbad

end ErdosSzekeres

end
