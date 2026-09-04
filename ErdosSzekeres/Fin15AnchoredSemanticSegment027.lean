module

public import ErdosSzekeres.Fin15AnchoredClauseChunk053
public import ErdosSzekeres.Fin15AnchoredClauseChunk054
public import ErdosSzekeres.Fin15AnchoredClauseChunk055

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 027. -/

theorem fin15Anchored_rejectSemanticSegment027
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      ((Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi))) ∨
      (((¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi)) ∨
      ((¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi)))) ∨
      ((((Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi)) ∨
      ((Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi))) ∨
      (((¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi)) ∨
      ((¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi))))) ∨
      (((((Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi)) ∨
      ((Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi))) ∨
      (((¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi)) ∨
      ((¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi)))) ∨
      ((((Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi)) ∨
      ((Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi))) ∨
      (((¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi) ∨
      (¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0448 chi)) ∨
      ((¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0448 chi)))))) ∨
      ((((((Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0448 chi) ∨
      (Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0448 chi)) ∨
      ((Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0448 chi) ∨
      (¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi))) ∨
      (((¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi)) ∨
      ((¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi)))) ∨
      ((((Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi)) ∨
      ((Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi))) ∨
      (((¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi)) ∨
      ((¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi))))) ∨
      (((((Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi)) ∨
      ((Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi))) ∨
      (((¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi)) ∨
      ((¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi)))) ∨
      ((((Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi)) ∨
      ((Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0452 chi))) ∨
      (((¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi)) ∨
      ((¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi))))))) ∨
      ((((((Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      ((Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0452 chi))) ∨
      (((¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi)) ∨
      ((¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi)))) ∨
      ((((Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0453 chi)) ∨
      ((Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0453 chi))) ∨
      (((¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0454 chi)) ∨
      ((¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0454 chi))))) ∨
      (((((Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0454 chi)) ∨
      ((Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi))) ∨
      (((¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi)))) ∨
      ((((Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi))) ∨
      (((¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi)) ∨
      ((¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi)))))) ∨
      ((((((Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi)) ∨
      ((Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi))) ∨
      (((¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi)) ∨
      ((¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi)))) ∨
      ((((Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi)) ∨
      ((Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi))) ∨
      (((¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi)) ∨
      ((¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi))))) ∨
      (((((Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi)) ∨
      ((Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi))) ∨
      (((¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi)) ∨
      ((¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi)))) ∨
      ((((Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi)) ∨
      ((Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi))) ∨
      (((¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi)) ∨
      ((¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0444 chi) ∨
      ((Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0444 chi))) ∨
      (((¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi)) ∨
      ((¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi)))) ∨
      ((((Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0445 chi)) ∨
      ((Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0445 chi))) ∨
      (((¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi)) ∨
      ((¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi))))) ∨
      (((((Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0449 chi)) ∨
      ((Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0449 chi))) ∨
      (((¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi)) ∨
      ((¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi)))) ∨
      ((((Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0450 chi)) ∨
      ((Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0450 chi))) ∨
      (((¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi)) ∨
      ((¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi)))))) ∨
      ((((((Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0451 chi)) ∨
      ((Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0451 chi))) ∨
      (((¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi)) ∨
      ((¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi)))) ∨
      ((((Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom0455 chi)) ∨
      ((Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom0455 chi))) ∨
      (((¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi)) ∨
      ((¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi))))) ∨
      (((((Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0446 chi)) ∨
      ((Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0446 chi))) ∨
      (((¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi)) ∨
      ((¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi)))) ∨
      ((((Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0447 chi)) ∨
      ((Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0448 chi))) ∨
      (((¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0448 chi) ∨
      (¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi)) ∨
      ((¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0448 chi) ∨
      (Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi))))))) ∨
      (((((((Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi) ∨
      (Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0448 chi)) ∨
      ((¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi))) ∨
      (((¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi)) ∨
      ((Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0449 chi)))) ∨
      ((((Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0449 chi)) ∨
      ((¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi))) ∨
      (((¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi)) ∨
      ((Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0450 chi))))) ∨
      (((((Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0450 chi)) ∨
      ((¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi))) ∨
      (((¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi)) ∨
      ((Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0451 chi)))) ∨
      ((((Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0451 chi)) ∨
      ((¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi))) ∨
      (((¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi)) ∨
      ((Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0452 chi)))))) ∨
      ((((((Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0452 chi)) ∨
      ((¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi))) ∨
      (((¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi)) ∨
      ((Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0453 chi)))) ∨
      ((((Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0453 chi)) ∨
      ((¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi))) ∨
      (((¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi)) ∨
      ((Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0454 chi))))) ∨
      (((((Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0454 chi)) ∨
      ((¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi))) ∨
      (((¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi)) ∨
      ((Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom0455 chi)))) ∨
      ((((Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi))) ∨
      (((¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi)) ∨
      ((Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom0452 chi)))))))))) := by
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
                exact fin15Anchored_clause06814 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06815 chi hone hbad
                ·
                  exact fin15Anchored_clause06816 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06817 chi hone hbad
                ·
                  exact fin15Anchored_clause06818 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06819 chi hone hbad
                ·
                  exact fin15Anchored_clause06820 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06821 chi hone hbad
                ·
                  exact fin15Anchored_clause06822 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06823 chi hone hbad
                ·
                  exact fin15Anchored_clause06824 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06825 chi hone hbad
                ·
                  exact fin15Anchored_clause06826 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06827 chi hone hbad
                ·
                  exact fin15Anchored_clause06828 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06829 chi hone hbad
                ·
                  exact fin15Anchored_clause06830 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06831 chi hone hbad
                ·
                  exact fin15Anchored_clause06832 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06833 chi hone hbad
                ·
                  exact fin15Anchored_clause06834 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06835 chi hone hbad
                ·
                  exact fin15Anchored_clause06836 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06837 chi hone hbad
                ·
                  exact fin15Anchored_clause06838 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06839 chi hone hbad
                ·
                  exact fin15Anchored_clause06840 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06841 chi hone hbad
                ·
                  exact fin15Anchored_clause06842 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06843 chi hone hbad
                ·
                  exact fin15Anchored_clause06844 chi hone hbad
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
                  exact fin15Anchored_clause06845 chi hone hbad
                ·
                  exact fin15Anchored_clause06846 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06847 chi hone hbad
                ·
                  exact fin15Anchored_clause06848 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06849 chi hone hbad
                ·
                  exact fin15Anchored_clause06850 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06851 chi hone hbad
                ·
                  exact fin15Anchored_clause06852 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06853 chi hone hbad
                ·
                  exact fin15Anchored_clause06854 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06855 chi hone hbad
                ·
                  exact fin15Anchored_clause06856 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06857 chi hone hbad
                ·
                  exact fin15Anchored_clause06858 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06859 chi hone hbad
                ·
                  exact fin15Anchored_clause06860 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06861 chi hone hbad
                ·
                  exact fin15Anchored_clause06862 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06863 chi hone hbad
                ·
                  exact fin15Anchored_clause06864 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06865 chi hone hbad
                ·
                  exact fin15Anchored_clause06866 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06867 chi hone hbad
                ·
                  exact fin15Anchored_clause06868 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06869 chi hone hbad
                ·
                  exact fin15Anchored_clause06870 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06871 chi hone hbad
                ·
                  exact fin15Anchored_clause06872 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06873 chi hone hbad
                ·
                  exact fin15Anchored_clause06874 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06875 chi hone hbad
                ·
                  exact fin15Anchored_clause06876 chi hone hbad
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
                exact fin15Anchored_clause06877 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06878 chi hone hbad
                ·
                  exact fin15Anchored_clause06879 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06880 chi hone hbad
                ·
                  exact fin15Anchored_clause06881 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06882 chi hone hbad
                ·
                  exact fin15Anchored_clause06883 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06884 chi hone hbad
                ·
                  exact fin15Anchored_clause06885 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06886 chi hone hbad
                ·
                  exact fin15Anchored_clause06887 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06888 chi hone hbad
                ·
                  exact fin15Anchored_clause06889 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06890 chi hone hbad
                ·
                  exact fin15Anchored_clause06891 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06892 chi hone hbad
                ·
                  exact fin15Anchored_clause06893 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06894 chi hone hbad
                ·
                  exact fin15Anchored_clause06895 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06896 chi hone hbad
                ·
                  exact fin15Anchored_clause06897 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06898 chi hone hbad
                ·
                  exact fin15Anchored_clause06899 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06900 chi hone hbad
                ·
                  exact fin15Anchored_clause06901 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06902 chi hone hbad
                ·
                  exact fin15Anchored_clause06903 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06904 chi hone hbad
                ·
                  exact fin15Anchored_clause06905 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06906 chi hone hbad
                ·
                  exact fin15Anchored_clause06907 chi hone hbad
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
                  exact fin15Anchored_clause06908 chi hone hbad
                ·
                  exact fin15Anchored_clause06909 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06910 chi hone hbad
                ·
                  exact fin15Anchored_clause06911 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06912 chi hone hbad
                ·
                  exact fin15Anchored_clause06913 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06914 chi hone hbad
                ·
                  exact fin15Anchored_clause06915 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06916 chi hone hbad
                ·
                  exact fin15Anchored_clause06917 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06918 chi hone hbad
                ·
                  exact fin15Anchored_clause06919 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06920 chi hone hbad
                ·
                  exact fin15Anchored_clause06921 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06922 chi hone hbad
                ·
                  exact fin15Anchored_clause06923 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06924 chi hone hbad
                ·
                  exact fin15Anchored_clause06925 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06926 chi hone hbad
                ·
                  exact fin15Anchored_clause06927 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06928 chi hone hbad
                ·
                  exact fin15Anchored_clause06929 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06930 chi hone hbad
                ·
                  exact fin15Anchored_clause06931 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06932 chi hone hbad
                ·
                  exact fin15Anchored_clause06933 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06934 chi hone hbad
                ·
                  exact fin15Anchored_clause06935 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06936 chi hone hbad
                ·
                  exact fin15Anchored_clause06937 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06938 chi hone hbad
                ·
                  exact fin15Anchored_clause06939 chi hone hbad
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
                exact fin15Anchored_clause06940 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06941 chi hone hbad
                ·
                  exact fin15Anchored_clause06942 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06943 chi hone hbad
                ·
                  exact fin15Anchored_clause06944 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06945 chi hone hbad
                ·
                  exact fin15Anchored_clause06946 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06947 chi hone hbad
                ·
                  exact fin15Anchored_clause06948 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06949 chi hone hbad
                ·
                  exact fin15Anchored_clause06950 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06951 chi hone hbad
                ·
                  exact fin15Anchored_clause06952 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06953 chi hone hbad
                ·
                  exact fin15Anchored_clause06954 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06955 chi hone hbad
                ·
                  exact fin15Anchored_clause06956 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06957 chi hone hbad
                ·
                  exact fin15Anchored_clause06958 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06959 chi hone hbad
                ·
                  exact fin15Anchored_clause06960 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06961 chi hone hbad
                ·
                  exact fin15Anchored_clause06962 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06963 chi hone hbad
                ·
                  exact fin15Anchored_clause06964 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06965 chi hone hbad
                ·
                  exact fin15Anchored_clause06966 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06967 chi hone hbad
                ·
                  exact fin15Anchored_clause06968 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06969 chi hone hbad
                ·
                  exact fin15Anchored_clause06970 chi hone hbad
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
                  exact fin15Anchored_clause06971 chi hone hbad
                ·
                  exact fin15Anchored_clause06972 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06973 chi hone hbad
                ·
                  exact fin15Anchored_clause06974 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06975 chi hone hbad
                ·
                  exact fin15Anchored_clause06976 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06977 chi hone hbad
                ·
                  exact fin15Anchored_clause06978 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06979 chi hone hbad
                ·
                  exact fin15Anchored_clause06980 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06981 chi hone hbad
                ·
                  exact fin15Anchored_clause06982 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06983 chi hone hbad
                ·
                  exact fin15Anchored_clause06984 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06985 chi hone hbad
                ·
                  exact fin15Anchored_clause06986 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06987 chi hone hbad
                ·
                  exact fin15Anchored_clause06988 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06989 chi hone hbad
                ·
                  exact fin15Anchored_clause06990 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06991 chi hone hbad
                ·
                  exact fin15Anchored_clause06992 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06993 chi hone hbad
                ·
                  exact fin15Anchored_clause06994 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06995 chi hone hbad
                ·
                  exact fin15Anchored_clause06996 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06997 chi hone hbad
                ·
                  exact fin15Anchored_clause06998 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06999 chi hone hbad
                ·
                  exact fin15Anchored_clause07000 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07001 chi hone hbad
                ·
                  exact fin15Anchored_clause07002 chi hone hbad
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
                  exact fin15Anchored_clause07003 chi hone hbad
                ·
                  exact fin15Anchored_clause07004 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07005 chi hone hbad
                ·
                  exact fin15Anchored_clause07006 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07007 chi hone hbad
                ·
                  exact fin15Anchored_clause07008 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07009 chi hone hbad
                ·
                  exact fin15Anchored_clause07010 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07011 chi hone hbad
                ·
                  exact fin15Anchored_clause07012 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07013 chi hone hbad
                ·
                  exact fin15Anchored_clause07014 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07015 chi hone hbad
                ·
                  exact fin15Anchored_clause07016 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07017 chi hone hbad
                ·
                  exact fin15Anchored_clause07018 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07019 chi hone hbad
                ·
                  exact fin15Anchored_clause07020 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07021 chi hone hbad
                ·
                  exact fin15Anchored_clause07022 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07023 chi hone hbad
                ·
                  exact fin15Anchored_clause07024 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07025 chi hone hbad
                ·
                  exact fin15Anchored_clause07026 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07027 chi hone hbad
                ·
                  exact fin15Anchored_clause07028 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07029 chi hone hbad
                ·
                  exact fin15Anchored_clause07030 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07031 chi hone hbad
                ·
                  exact fin15Anchored_clause07032 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07033 chi hone hbad
                ·
                  exact fin15Anchored_clause07034 chi hone hbad
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
                  exact fin15Anchored_clause07035 chi hone hbad
                ·
                  exact fin15Anchored_clause07036 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07037 chi hone hbad
                ·
                  exact fin15Anchored_clause07038 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07039 chi hone hbad
                ·
                  exact fin15Anchored_clause07040 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07041 chi hone hbad
                ·
                  exact fin15Anchored_clause07042 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07043 chi hone hbad
                ·
                  exact fin15Anchored_clause07044 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07045 chi hone hbad
                ·
                  exact fin15Anchored_clause07046 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07047 chi hone hbad
                ·
                  exact fin15Anchored_clause07048 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07049 chi hone hbad
                ·
                  exact fin15Anchored_clause07050 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07051 chi hone hbad
                ·
                  exact fin15Anchored_clause07052 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07053 chi hone hbad
                ·
                  exact fin15Anchored_clause07054 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07055 chi hone hbad
                ·
                  exact fin15Anchored_clause07056 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07057 chi hone hbad
                ·
                  exact fin15Anchored_clause07058 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07059 chi hone hbad
                ·
                  exact fin15Anchored_clause07060 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07061 chi hone hbad
                ·
                  exact fin15Anchored_clause07062 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07063 chi hone hbad
                ·
                  exact fin15Anchored_clause07064 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause07065 chi hone hbad
                ·
                  exact fin15Anchored_clause07066 chi hone hbad

end ErdosSzekeres

end
