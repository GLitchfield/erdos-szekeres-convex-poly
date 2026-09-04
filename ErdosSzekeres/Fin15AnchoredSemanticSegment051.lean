module

public import ErdosSzekeres.Fin15AnchoredClauseChunk100
public import ErdosSzekeres.Fin15AnchoredClauseChunk101
public import ErdosSzekeres.Fin15AnchoredClauseChunk102

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 051. -/

theorem fin15Anchored_rejectSemanticSegment051
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi))) ∨
      (((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1504 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1504 chi)))) ∨
      ((((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi))) ∨
      (((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi))))) ∨
      (((((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1505 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1506 chi))) ∨
      (((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1506 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1506 chi)) ∨
      ((¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1506 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1506 chi)))) ∨
      ((((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1506 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1506 chi)) ∨
      ((Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1506 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1506 chi))) ∨
      (((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1507 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi)) ∨
      ((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1507 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi)) ∨
      ((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi))) ∨
      (((Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1507 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi)) ∨
      ((Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1507 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1509 chi)))) ∨
      ((((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1509 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1509 chi)) ∨
      ((¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1509 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1509 chi))) ∨
      (((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1509 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1509 chi)) ∨
      ((Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1509 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1509 chi))))) ∨
      (((((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1510 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1510 chi)) ∨
      ((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1510 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1510 chi))) ∨
      (((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1510 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1510 chi)) ∨
      ((Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1510 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1510 chi)))) ∨
      ((((Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1510 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1511 chi)) ∨
      ((¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1511 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1511 chi))) ∨
      (((¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1511 chi) ∨
      (¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1511 chi)) ∨
      ((Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1511 chi) ∨
      (Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1511 chi))))))) ∨
      ((((((Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1511 chi) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1512 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1512 chi))) ∨
      (((¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1512 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1512 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1512 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1512 chi)))) ∨
      ((((Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1512 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1512 chi)) ∨
      ((Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1512 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1513 chi))) ∨
      (((¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1513 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi))))) ∨
      (((((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1513 chi)) ∨
      ((Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1513 chi))) ∨
      (((Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1513 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1514 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1514 chi)))) ∨
      ((((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi))) ∨
      (((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1514 chi)) ∨
      ((Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1514 chi)))))) ∨
      ((((((Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1514 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1515 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1515 chi))) ∨
      (((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi)))) ∨
      ((((Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi)) ∨
      ((Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1515 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1515 chi))) ∨
      (((Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1515 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1516 chi)) ∨
      ((¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1516 chi) ∨
      (¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1516 chi))))) ∨
      (((((¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1516 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1516 chi)) ∨
      ((Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1516 chi) ∨
      (Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1516 chi))) ∨
      (((Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1516 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1517 chi)) ∨
      ((¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1517 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1517 chi)))) ∨
      ((((Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1517 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1518 chi)) ∨
      ((¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1518 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1518 chi))) ∨
      (((¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1518 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1518 chi)) ∨
      ((Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1518 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1518 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1518 chi) ∨
      ((¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1519 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi))) ∨
      (((¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1519 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi)) ∨
      ((¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi)))) ∨
      ((((Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1519 chi)) ∨
      ((Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1519 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1519 chi))) ∨
      (((¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1520 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi)) ∨
      ((¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi) ∨
      (¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1520 chi))))) ∨
      (((((¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi)) ∨
      ((Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1520 chi))) ∨
      (((Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1520 chi) ∨
      (Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1520 chi)) ∨
      ((¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1521 chi) ∨
      (¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1521 chi)))) ∨
      ((((¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1521 chi) ∨
      (Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1521 chi)) ∨
      ((Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1521 chi) ∨
      (Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1521 chi))) ∨
      (((¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1522 chi) ∨
      (Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1522 chi)) ∨
      ((Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1522 chi) ∨
      (¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom1523 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1524 chi) ∨
      (¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi)) ∨
      ((¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1524 chi) ∨
      (¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi))) ∨
      (((¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) ∨
      (¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi)) ∨
      ((Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) ∨
      (Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi)))) ∨
      ((((Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) ∨
      (Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1524 chi)) ∨
      ((Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi) ∨
      (Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1524 chi))) ∨
      (((Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1524 chi) ∨
      (¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1525 chi)) ∨
      ((¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1525 chi) ∨
      (¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1525 chi))))) ∨
      (((((¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1525 chi) ∨
      (Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1525 chi)) ∨
      ((Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1525 chi) ∨
      (Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1525 chi))) ∨
      (((Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1525 chi) ∨
      (Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1525 chi)) ∨
      ((¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1526 chi) ∨
      (¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1526 chi)))) ∨
      ((((¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1526 chi) ∨
      (¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1526 chi)) ∨
      ((¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1526 chi) ∨
      (Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1526 chi))) ∨
      (((Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1526 chi) ∨
      (Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1526 chi)) ∨
      ((Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1526 chi) ∨
      (Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1526 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1527 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1527 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi)))) ∨
      ((((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1527 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1527 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1527 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1528 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1528 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1528 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1528 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1528 chi))))) ∨
      (((((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1528 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1528 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1528 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1528 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1529 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1529 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1529 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1529 chi)))) ∨
      ((((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1529 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1529 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1529 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1529 chi))) ∨
      (((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1529 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1530 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1530 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi))) ∨
      (((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1530 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1530 chi)))) ∨
      ((((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1530 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1531 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1531 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi))))) ∨
      (((((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1531 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1531 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1531 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1532 chi))) ∨
      (((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1532 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi)))) ∨
      ((((Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi)) ∨
      ((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1532 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi))) ∨
      (((Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1532 chi) ∨
      (Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1532 chi)) ∨
      ((¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1533 chi) ∨
      (¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1533 chi)))))))))) := by
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
                exact fin15Anchored_clause12871 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12872 chi hbad
                ·
                  exact fin15Anchored_clause12873 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12874 chi hbad
                ·
                  exact fin15Anchored_clause12875 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12876 chi hbad
                ·
                  exact fin15Anchored_clause12877 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12878 chi hbad
                ·
                  exact fin15Anchored_clause12879 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12880 chi hbad
                ·
                  exact fin15Anchored_clause12881 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12882 chi hbad
                ·
                  exact fin15Anchored_clause12883 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12884 chi hbad
                ·
                  exact fin15Anchored_clause12885 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12886 chi hbad
                ·
                  exact fin15Anchored_clause12887 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12888 chi hbad
                ·
                  exact fin15Anchored_clause12889 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12890 chi hbad
                ·
                  exact fin15Anchored_clause12891 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12892 chi hbad
                ·
                  exact fin15Anchored_clause12893 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12894 chi hbad
                ·
                  exact fin15Anchored_clause12895 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12896 chi hbad
                ·
                  exact fin15Anchored_clause12897 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12898 chi hbad
                ·
                  exact fin15Anchored_clause12899 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12900 chi hbad
                ·
                  exact fin15Anchored_clause12901 chi hbad
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
                  exact fin15Anchored_clause12902 chi hbad
                ·
                  exact fin15Anchored_clause12903 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12904 chi hbad
                ·
                  exact fin15Anchored_clause12905 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12906 chi hbad
                ·
                  exact fin15Anchored_clause12907 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12908 chi hbad
                ·
                  exact fin15Anchored_clause12909 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12910 chi hbad
                ·
                  exact fin15Anchored_clause12911 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12912 chi hbad
                ·
                  exact fin15Anchored_clause12913 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12914 chi hbad
                ·
                  exact fin15Anchored_clause12915 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12916 chi hbad
                ·
                  exact fin15Anchored_clause12917 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12918 chi hbad
                ·
                  exact fin15Anchored_clause12919 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12920 chi hbad
                ·
                  exact fin15Anchored_clause12921 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12922 chi hbad
                ·
                  exact fin15Anchored_clause12923 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12924 chi hbad
                ·
                  exact fin15Anchored_clause12925 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12926 chi hbad
                ·
                  exact fin15Anchored_clause12927 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12928 chi hbad
                ·
                  exact fin15Anchored_clause12929 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12930 chi hbad
                ·
                  exact fin15Anchored_clause12931 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12932 chi hbad
                ·
                  exact fin15Anchored_clause12933 chi hbad
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
                exact fin15Anchored_clause12934 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12935 chi hbad
                ·
                  exact fin15Anchored_clause12936 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12937 chi hbad
                ·
                  exact fin15Anchored_clause12938 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12939 chi hbad
                ·
                  exact fin15Anchored_clause12940 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12941 chi hbad
                ·
                  exact fin15Anchored_clause12942 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12943 chi hbad
                ·
                  exact fin15Anchored_clause12944 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12945 chi hbad
                ·
                  exact fin15Anchored_clause12946 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12947 chi hbad
                ·
                  exact fin15Anchored_clause12948 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12949 chi hbad
                ·
                  exact fin15Anchored_clause12950 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12951 chi hbad
                ·
                  exact fin15Anchored_clause12952 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12953 chi hbad
                ·
                  exact fin15Anchored_clause12954 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12955 chi hbad
                ·
                  exact fin15Anchored_clause12956 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12957 chi hbad
                ·
                  exact fin15Anchored_clause12958 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12959 chi hbad
                ·
                  exact fin15Anchored_clause12960 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12961 chi hbad
                ·
                  exact fin15Anchored_clause12962 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12963 chi hbad
                ·
                  exact fin15Anchored_clause12964 chi hbad
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
                  exact fin15Anchored_clause12965 chi hbad
                ·
                  exact fin15Anchored_clause12966 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12967 chi hbad
                ·
                  exact fin15Anchored_clause12968 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12969 chi hbad
                ·
                  exact fin15Anchored_clause12970 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12971 chi hbad
                ·
                  exact fin15Anchored_clause12972 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12973 chi hbad
                ·
                  exact fin15Anchored_clause12974 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12975 chi hbad
                ·
                  exact fin15Anchored_clause12976 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12977 chi hbad
                ·
                  exact fin15Anchored_clause12978 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12979 chi hbad
                ·
                  exact fin15Anchored_clause12980 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12981 chi hbad
                ·
                  exact fin15Anchored_clause12982 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12983 chi hbad
                ·
                  exact fin15Anchored_clause12984 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12985 chi hbad
                ·
                  exact fin15Anchored_clause12986 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12987 chi hbad
                ·
                  exact fin15Anchored_clause12988 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12989 chi hbad
                ·
                  exact fin15Anchored_clause12990 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12991 chi hbad
                ·
                  exact fin15Anchored_clause12992 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12993 chi hbad
                ·
                  exact fin15Anchored_clause12994 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12995 chi hbad
                ·
                  exact fin15Anchored_clause12996 chi hbad
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
                exact fin15Anchored_clause12997 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12998 chi hbad
                ·
                  exact fin15Anchored_clause12999 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13000 chi hbad
                ·
                  exact fin15Anchored_clause13001 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13002 chi hbad
                ·
                  exact fin15Anchored_clause13003 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13004 chi hbad
                ·
                  exact fin15Anchored_clause13005 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13006 chi hbad
                ·
                  exact fin15Anchored_clause13007 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13008 chi hbad
                ·
                  exact fin15Anchored_clause13009 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13010 chi hbad
                ·
                  exact fin15Anchored_clause13011 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13012 chi hbad
                ·
                  exact fin15Anchored_clause13013 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13014 chi hbad
                ·
                  exact fin15Anchored_clause13015 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13016 chi hbad
                ·
                  exact fin15Anchored_clause13017 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13018 chi hbad
                ·
                  exact fin15Anchored_clause13019 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13020 chi hbad
                ·
                  exact fin15Anchored_clause13021 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13022 chi hbad
                ·
                  exact fin15Anchored_clause13023 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13024 chi hbad
                ·
                  exact fin15Anchored_clause13025 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13026 chi hbad
                ·
                  exact fin15Anchored_clause13027 chi hbad
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
                  exact fin15Anchored_clause13028 chi hbad
                ·
                  exact fin15Anchored_clause13029 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13030 chi hbad
                ·
                  exact fin15Anchored_clause13031 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13032 chi hbad
                ·
                  exact fin15Anchored_clause13033 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13034 chi hbad
                ·
                  exact fin15Anchored_clause13035 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13036 chi hbad
                ·
                  exact fin15Anchored_clause13037 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13038 chi hbad
                ·
                  exact fin15Anchored_clause13039 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13040 chi hbad
                ·
                  exact fin15Anchored_clause13041 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13042 chi hbad
                ·
                  exact fin15Anchored_clause13043 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13044 chi hbad
                ·
                  exact fin15Anchored_clause13045 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13046 chi hbad
                ·
                  exact fin15Anchored_clause13047 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13048 chi hbad
                ·
                  exact fin15Anchored_clause13049 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13050 chi hbad
                ·
                  exact fin15Anchored_clause13051 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13052 chi hbad
                ·
                  exact fin15Anchored_clause13053 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13054 chi hbad
                ·
                  exact fin15Anchored_clause13055 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13056 chi hbad
                ·
                  exact fin15Anchored_clause13057 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13058 chi hbad
                ·
                  exact fin15Anchored_clause13059 chi hbad
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
                  exact fin15Anchored_clause13060 chi hbad
                ·
                  exact fin15Anchored_clause13061 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13062 chi hbad
                ·
                  exact fin15Anchored_clause13063 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13064 chi hbad
                ·
                  exact fin15Anchored_clause13065 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13066 chi hbad
                ·
                  exact fin15Anchored_clause13067 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13068 chi hbad
                ·
                  exact fin15Anchored_clause13069 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13070 chi hbad
                ·
                  exact fin15Anchored_clause13071 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13072 chi hbad
                ·
                  exact fin15Anchored_clause13073 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13074 chi hbad
                ·
                  exact fin15Anchored_clause13075 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13076 chi hbad
                ·
                  exact fin15Anchored_clause13077 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13078 chi hbad
                ·
                  exact fin15Anchored_clause13079 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13080 chi hbad
                ·
                  exact fin15Anchored_clause13081 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13082 chi hbad
                ·
                  exact fin15Anchored_clause13083 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13084 chi hbad
                ·
                  exact fin15Anchored_clause13085 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13086 chi hbad
                ·
                  exact fin15Anchored_clause13087 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13088 chi hbad
                ·
                  exact fin15Anchored_clause13089 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13090 chi hbad
                ·
                  exact fin15Anchored_clause13091 chi hbad
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
                  exact fin15Anchored_clause13092 chi hbad
                ·
                  exact fin15Anchored_clause13093 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13094 chi hbad
                ·
                  exact fin15Anchored_clause13095 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13096 chi hbad
                ·
                  exact fin15Anchored_clause13097 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13098 chi hbad
                ·
                  exact fin15Anchored_clause13099 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13100 chi hbad
                ·
                  exact fin15Anchored_clause13101 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13102 chi hbad
                ·
                  exact fin15Anchored_clause13103 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13104 chi hbad
                ·
                  exact fin15Anchored_clause13105 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13106 chi hbad
                ·
                  exact fin15Anchored_clause13107 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13108 chi hbad
                ·
                  exact fin15Anchored_clause13109 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13110 chi hbad
                ·
                  exact fin15Anchored_clause13111 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13112 chi hbad
                ·
                  exact fin15Anchored_clause13113 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13114 chi hbad
                ·
                  exact fin15Anchored_clause13115 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13116 chi hbad
                ·
                  exact fin15Anchored_clause13117 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13118 chi hbad
                ·
                  exact fin15Anchored_clause13119 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13120 chi hbad
                ·
                  exact fin15Anchored_clause13121 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13122 chi hbad
                ·
                  exact fin15Anchored_clause13123 chi hbad

end ErdosSzekeres

end
