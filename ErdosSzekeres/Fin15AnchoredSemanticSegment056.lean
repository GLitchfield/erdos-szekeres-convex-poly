module

public import ErdosSzekeres.Fin15AnchoredClauseChunk110
public import ErdosSzekeres.Fin15AnchoredClauseChunk111
public import ErdosSzekeres.Fin15AnchoredClauseChunk112

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 056. -/

theorem fin15Anchored_rejectSemanticSegment056
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi) ∨
      ((Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1653 chi) ∨
      (Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1653 chi))) ∨
      (((Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1653 chi) ∨
      (¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1654 chi)) ∨
      ((¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi) ∨
      (¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1654 chi)))) ∨
      ((((¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi) ∨
      (¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi)) ∨
      ((Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi) ∨
      (Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1654 chi))) ∨
      (((Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi) ∨
      (Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1654 chi)) ∨
      ((Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1654 chi) ∨
      (¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1655 chi))))) ∨
      (((((¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1656 chi) ∨
      (Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1656 chi)) ∨
      ((¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1657 chi) ∨
      (¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi))) ∨
      (((¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1657 chi) ∨
      (¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi)) ∨
      ((¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi) ∨
      (¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi)))) ∨
      ((((Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi) ∨
      (Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi)) ∨
      ((Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1657 chi) ∨
      (Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1657 chi))) ∨
      (((Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1657 chi) ∨
      (¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1658 chi)) ∨
      ((¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi) ∨
      (¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1658 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi) ∨
      (¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi)) ∨
      ((Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi) ∨
      (Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi))) ∨
      (((Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1658 chi) ∨
      (Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1658 chi)) ∨
      ((Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1658 chi) ∨
      (¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1659 chi)))) ∨
      ((((¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi) ∨
      (¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1659 chi)) ∨
      ((¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi) ∨
      (¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi))) ∨
      (((Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi) ∨
      (Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi)) ∨
      ((Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1659 chi) ∨
      (Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1659 chi))))) ∨
      (((((Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1659 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1660 chi)) ∨
      ((¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1660 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1660 chi))) ∨
      (((¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1660 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1660 chi)) ∨
      ((Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1660 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1660 chi)))) ∨
      ((((Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1660 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1660 chi)) ∨
      ((¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1662 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi))) ∨
      (((¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1662 chi)) ∨
      ((¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi))))))) ∨
      ((((((Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi) ∨
      ((Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1662 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1662 chi))) ∨
      (((¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1663 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1663 chi)) ∨
      ((¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1663 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1663 chi)))) ∨
      ((((¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1663 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1663 chi)) ∨
      ((Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1663 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1664 chi))) ∨
      (((¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi)) ∨
      ((¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1664 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi))))) ∨
      (((((¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi)) ∨
      ((Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1664 chi))) ∨
      (((Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1664 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1664 chi)) ∨
      ((¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1666 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi)))) ∨
      ((((¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1666 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi)) ∨
      ((¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi))) ∨
      (((Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1666 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi)) ∨
      ((Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1666 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1666 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1667 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi)) ∨
      ((¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1667 chi))) ∨
      (((¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi)) ∨
      ((Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1667 chi)))) ∨
      ((((Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1667 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1667 chi)) ∨
      ((¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1668 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi))) ∨
      (((¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1668 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi)) ∨
      ((¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi))))) ∨
      (((((Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1668 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi)) ∨
      ((Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1668 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1668 chi))) ∨
      (((¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1672 chi) ∨
      (¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi)) ∨
      ((¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1672 chi) ∨
      (¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi)))) ∨
      ((((¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) ∨
      (¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi)) ∨
      ((Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) ∨
      (Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi))) ∨
      (((Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) ∨
      (Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1672 chi)) ∨
      ((Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1672 chi) ∨
      (Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1672 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1673 chi) ∨
      ((¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi) ∨
      (¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi))) ∨
      (((¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1673 chi) ∨
      (¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi)) ∨
      ((¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi) ∨
      (Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi)))) ∨
      ((((Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi) ∨
      (Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1673 chi)) ∨
      ((Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1673 chi) ∨
      (Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1673 chi))) ∨
      (((¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1674 chi) ∨
      (¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi)) ∨
      ((¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1674 chi) ∨
      (¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi))))) ∨
      (((((¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) ∨
      (¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi)) ∨
      ((Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) ∨
      (Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi))) ∨
      (((Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) ∨
      (Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1674 chi)) ∨
      ((Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1674 chi) ∨
      (Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1674 chi)))) ∨
      ((((¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1675 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1675 chi)) ∨
      ((¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1675 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1675 chi))) ∨
      (((¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1675 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1675 chi)) ∨
      ((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1675 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1675 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1676 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi)) ∨
      ((¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1676 chi))) ∨
      (((¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi)) ∨
      ((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi)))) ∨
      ((((Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1676 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1676 chi)) ∨
      ((Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1676 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1677 chi))) ∨
      (((¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1677 chi)) ∨
      ((¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi))))) ∨
      (((((¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi)) ∨
      ((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1677 chi))) ∨
      (((Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1677 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1677 chi)) ∨
      ((¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1678 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi)))) ∨
      ((((¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1678 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi)) ∨
      ((¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi))) ∨
      (((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1678 chi)) ∨
      ((Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1678 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1678 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1679 chi) ∨
      ((¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi) ∨
      (¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi))) ∨
      (((¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1679 chi) ∨
      (¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi)) ∨
      ((¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi) ∨
      (Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi)))) ∨
      ((((Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1679 chi) ∨
      (Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1679 chi)) ∨
      ((¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1680 chi) ∨
      (¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1680 chi))) ∨
      (((¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1680 chi) ∨
      (Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1680 chi)) ∨
      ((Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1680 chi) ∨
      (Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1680 chi))))) ∨
      (((((¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1681 chi) ∨
      (Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1681 chi)) ∨
      ((¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1682 chi) ∨
      (¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi))) ∨
      (((¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1682 chi) ∨
      (¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi)) ∨
      ((¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi) ∨
      (Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi)))) ∨
      ((((Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi) ∨
      (Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1682 chi)) ∨
      ((Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1682 chi) ∨
      (Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1682 chi))) ∨
      (((¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1683 chi) ∨
      (¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi)) ∨
      ((¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1683 chi) ∨
      (¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi) ∨
      (¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi)) ∨
      ((Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi) ∨
      (Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1683 chi))) ∨
      (((Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1683 chi) ∨
      (Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1683 chi)) ∨
      ((¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1684 chi) ∨
      (¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi)))) ∨
      ((((¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1684 chi) ∨
      (¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi)) ∨
      ((Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi) ∨
      (Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi))) ∨
      (((Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1684 chi) ∨
      (Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi)) ∨
      ((Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1684 chi) ∨
      (Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1684 chi))))) ∨
      (((((¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1685 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi)) ∨
      ((¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1685 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi))) ∨
      (((¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi)) ∨
      ((Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi) ∨
      (Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1685 chi)))) ∨
      ((((Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1685 chi) ∨
      (Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1685 chi)) ∨
      ((¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1686 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1686 chi))) ∨
      (((¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1686 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1686 chi)) ∨
      ((¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1686 chi) ∨
      (Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1686 chi)))))))))) := by
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
                exact fin15Anchored_clause14134 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14135 chi hbad
                ·
                  exact fin15Anchored_clause14136 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14137 chi hbad
                ·
                  exact fin15Anchored_clause14138 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14139 chi hbad
                ·
                  exact fin15Anchored_clause14140 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14141 chi hbad
                ·
                  exact fin15Anchored_clause14142 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14143 chi hbad
                ·
                  exact fin15Anchored_clause14144 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14145 chi hbad
                ·
                  exact fin15Anchored_clause14146 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14147 chi hbad
                ·
                  exact fin15Anchored_clause14148 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14149 chi hbad
                ·
                  exact fin15Anchored_clause14150 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14151 chi hbad
                ·
                  exact fin15Anchored_clause14152 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14153 chi hbad
                ·
                  exact fin15Anchored_clause14154 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14155 chi hbad
                ·
                  exact fin15Anchored_clause14156 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14157 chi hbad
                ·
                  exact fin15Anchored_clause14158 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14159 chi hbad
                ·
                  exact fin15Anchored_clause14160 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14161 chi hbad
                ·
                  exact fin15Anchored_clause14162 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14163 chi hbad
                ·
                  exact fin15Anchored_clause14164 chi hbad
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
                  exact fin15Anchored_clause14165 chi hbad
                ·
                  exact fin15Anchored_clause14166 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14167 chi hbad
                ·
                  exact fin15Anchored_clause14168 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14169 chi hbad
                ·
                  exact fin15Anchored_clause14170 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14171 chi hbad
                ·
                  exact fin15Anchored_clause14172 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14173 chi hbad
                ·
                  exact fin15Anchored_clause14174 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14175 chi hbad
                ·
                  exact fin15Anchored_clause14176 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14177 chi hbad
                ·
                  exact fin15Anchored_clause14178 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14179 chi hbad
                ·
                  exact fin15Anchored_clause14180 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14181 chi hbad
                ·
                  exact fin15Anchored_clause14182 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14183 chi hbad
                ·
                  exact fin15Anchored_clause14184 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14185 chi hbad
                ·
                  exact fin15Anchored_clause14186 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14187 chi hbad
                ·
                  exact fin15Anchored_clause14188 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14189 chi hbad
                ·
                  exact fin15Anchored_clause14190 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14191 chi hbad
                ·
                  exact fin15Anchored_clause14192 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14193 chi hbad
                ·
                  exact fin15Anchored_clause14194 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14195 chi hbad
                ·
                  exact fin15Anchored_clause14196 chi hbad
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
                exact fin15Anchored_clause14197 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14198 chi hbad
                ·
                  exact fin15Anchored_clause14199 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14200 chi hbad
                ·
                  exact fin15Anchored_clause14201 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14202 chi hbad
                ·
                  exact fin15Anchored_clause14203 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14204 chi hbad
                ·
                  exact fin15Anchored_clause14205 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14206 chi hbad
                ·
                  exact fin15Anchored_clause14207 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14208 chi hbad
                ·
                  exact fin15Anchored_clause14209 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14210 chi hbad
                ·
                  exact fin15Anchored_clause14211 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14212 chi hbad
                ·
                  exact fin15Anchored_clause14213 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14214 chi hbad
                ·
                  exact fin15Anchored_clause14215 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14216 chi hbad
                ·
                  exact fin15Anchored_clause14217 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14218 chi hbad
                ·
                  exact fin15Anchored_clause14219 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14220 chi hbad
                ·
                  exact fin15Anchored_clause14221 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14222 chi hbad
                ·
                  exact fin15Anchored_clause14223 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14224 chi hbad
                ·
                  exact fin15Anchored_clause14225 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14226 chi hbad
                ·
                  exact fin15Anchored_clause14227 chi hbad
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
                  exact fin15Anchored_clause14228 chi hbad
                ·
                  exact fin15Anchored_clause14229 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14230 chi hbad
                ·
                  exact fin15Anchored_clause14231 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14232 chi hbad
                ·
                  exact fin15Anchored_clause14233 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14234 chi hbad
                ·
                  exact fin15Anchored_clause14235 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14236 chi hbad
                ·
                  exact fin15Anchored_clause14237 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14238 chi hbad
                ·
                  exact fin15Anchored_clause14239 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14240 chi hbad
                ·
                  exact fin15Anchored_clause14241 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14242 chi hbad
                ·
                  exact fin15Anchored_clause14243 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14244 chi hbad
                ·
                  exact fin15Anchored_clause14245 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14246 chi hbad
                ·
                  exact fin15Anchored_clause14247 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14248 chi hbad
                ·
                  exact fin15Anchored_clause14249 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14250 chi hbad
                ·
                  exact fin15Anchored_clause14251 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14252 chi hbad
                ·
                  exact fin15Anchored_clause14253 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14254 chi hbad
                ·
                  exact fin15Anchored_clause14255 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14256 chi hbad
                ·
                  exact fin15Anchored_clause14257 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14258 chi hbad
                ·
                  exact fin15Anchored_clause14259 chi hbad
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
                exact fin15Anchored_clause14260 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14261 chi hbad
                ·
                  exact fin15Anchored_clause14262 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14263 chi hbad
                ·
                  exact fin15Anchored_clause14264 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14265 chi hbad
                ·
                  exact fin15Anchored_clause14266 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14267 chi hbad
                ·
                  exact fin15Anchored_clause14268 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14269 chi hbad
                ·
                  exact fin15Anchored_clause14270 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14271 chi hbad
                ·
                  exact fin15Anchored_clause14272 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14273 chi hbad
                ·
                  exact fin15Anchored_clause14274 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14275 chi hbad
                ·
                  exact fin15Anchored_clause14276 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14277 chi hbad
                ·
                  exact fin15Anchored_clause14278 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14279 chi hbad
                ·
                  exact fin15Anchored_clause14280 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14281 chi hbad
                ·
                  exact fin15Anchored_clause14282 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14283 chi hbad
                ·
                  exact fin15Anchored_clause14284 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14285 chi hbad
                ·
                  exact fin15Anchored_clause14286 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14287 chi hbad
                ·
                  exact fin15Anchored_clause14288 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14289 chi hbad
                ·
                  exact fin15Anchored_clause14290 chi hbad
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
                  exact fin15Anchored_clause14291 chi hbad
                ·
                  exact fin15Anchored_clause14292 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14293 chi hbad
                ·
                  exact fin15Anchored_clause14294 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14295 chi hbad
                ·
                  exact fin15Anchored_clause14296 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14297 chi hbad
                ·
                  exact fin15Anchored_clause14298 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14299 chi hbad
                ·
                  exact fin15Anchored_clause14300 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14301 chi hbad
                ·
                  exact fin15Anchored_clause14302 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14303 chi hbad
                ·
                  exact fin15Anchored_clause14304 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14305 chi hbad
                ·
                  exact fin15Anchored_clause14306 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14307 chi hbad
                ·
                  exact fin15Anchored_clause14308 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14309 chi hbad
                ·
                  exact fin15Anchored_clause14310 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14311 chi hbad
                ·
                  exact fin15Anchored_clause14312 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14313 chi hbad
                ·
                  exact fin15Anchored_clause14314 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14315 chi hbad
                ·
                  exact fin15Anchored_clause14316 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14317 chi hbad
                ·
                  exact fin15Anchored_clause14318 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14319 chi hbad
                ·
                  exact fin15Anchored_clause14320 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14321 chi hbad
                ·
                  exact fin15Anchored_clause14322 chi hbad
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
                exact fin15Anchored_clause14323 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14324 chi hbad
                ·
                  exact fin15Anchored_clause14325 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14326 chi hbad
                ·
                  exact fin15Anchored_clause14327 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14328 chi hbad
                ·
                  exact fin15Anchored_clause14329 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14330 chi hbad
                ·
                  exact fin15Anchored_clause14331 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14332 chi hbad
                ·
                  exact fin15Anchored_clause14333 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14334 chi hbad
                ·
                  exact fin15Anchored_clause14335 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14336 chi hbad
                ·
                  exact fin15Anchored_clause14337 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14338 chi hbad
                ·
                  exact fin15Anchored_clause14339 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14340 chi hbad
                ·
                  exact fin15Anchored_clause14341 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14342 chi hbad
                ·
                  exact fin15Anchored_clause14343 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14344 chi hbad
                ·
                  exact fin15Anchored_clause14345 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14346 chi hbad
                ·
                  exact fin15Anchored_clause14347 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14348 chi hbad
                ·
                  exact fin15Anchored_clause14349 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14350 chi hbad
                ·
                  exact fin15Anchored_clause14351 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14352 chi hbad
                ·
                  exact fin15Anchored_clause14353 chi hbad
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
                  exact fin15Anchored_clause14354 chi hbad
                ·
                  exact fin15Anchored_clause14355 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14356 chi hbad
                ·
                  exact fin15Anchored_clause14357 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14358 chi hbad
                ·
                  exact fin15Anchored_clause14359 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14360 chi hbad
                ·
                  exact fin15Anchored_clause14361 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14362 chi hbad
                ·
                  exact fin15Anchored_clause14363 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14364 chi hbad
                ·
                  exact fin15Anchored_clause14365 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14366 chi hbad
                ·
                  exact fin15Anchored_clause14367 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14368 chi hbad
                ·
                  exact fin15Anchored_clause14369 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14370 chi hbad
                ·
                  exact fin15Anchored_clause14371 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14372 chi hbad
                ·
                  exact fin15Anchored_clause14373 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14374 chi hbad
                ·
                  exact fin15Anchored_clause14375 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14376 chi hbad
                ·
                  exact fin15Anchored_clause14377 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14378 chi hbad
                ·
                  exact fin15Anchored_clause14379 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14380 chi hbad
                ·
                  exact fin15Anchored_clause14381 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14382 chi hbad
                ·
                  exact fin15Anchored_clause14383 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14384 chi hbad
                ·
                  exact fin15Anchored_clause14385 chi hbad

end ErdosSzekeres

end
