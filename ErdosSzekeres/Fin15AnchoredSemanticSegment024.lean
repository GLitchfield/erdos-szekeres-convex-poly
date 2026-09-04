module

public import ErdosSzekeres.Fin15AnchoredClauseChunk047
public import ErdosSzekeres.Fin15AnchoredClauseChunk048
public import ErdosSzekeres.Fin15AnchoredClauseChunk049

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 024. -/

theorem fin15Anchored_rejectSemanticSegment024
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      ((Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi))) ∨
      (((¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi)) ∨
      ((¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi)))) ∨
      ((((Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi)) ∨
      ((Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0424 chi))) ∨
      (((¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0424 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi)) ∨
      ((¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0424 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi))))) ∨
      (((((Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0424 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi)) ∨
      ((Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0424 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi))) ∨
      (((¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi) ∨
      (¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi)) ∨
      ((¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi)))) ∨
      ((((Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0425 chi) ∨
      (Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi)) ∨
      ((Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0425 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi))) ∨
      (((¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi)) ∨
      ((¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi)))))) ∨
      ((((((Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi)) ∨
      ((Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0427 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi))) ∨
      (((¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi)) ∨
      ((¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi)))) ∨
      ((((Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi)) ∨
      ((Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0428 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi))) ∨
      (((¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi)) ∨
      ((¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi))))) ∨
      (((((Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi)) ∨
      ((Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0429 chi) ∨
      (¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi))) ∨
      (((¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi)) ∨
      ((¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi)))) ∨
      ((((Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi)) ∨
      ((Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi))) ∨
      (((¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi)) ∨
      ((¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi))))))) ∨
      ((((((Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      ((Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0434 chi))) ∨
      (((¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi)) ∨
      ((¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi)))) ∨
      ((((Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0435 chi)) ∨
      ((Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0435 chi))) ∨
      (((¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi)) ∨
      ((¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi))))) ∨
      (((((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0436 chi)) ∨
      ((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0436 chi))) ∨
      (((¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi)) ∨
      ((¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi)))) ∨
      ((((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi)) ∨
      ((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi))) ∨
      (((¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi)) ∨
      ((¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi)))))) ∨
      ((((((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi)) ∨
      ((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi))) ∨
      (((¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi)) ∨
      ((¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi)))) ∨
      ((((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi)) ∨
      ((Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi))) ∨
      (((¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi)) ∨
      ((¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi))))) ∨
      (((((Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi)) ∨
      ((Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi))) ∨
      (((¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi) ∨
      (¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi)) ∨
      ((¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi) ∨
      (¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi)))) ∨
      ((((Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi) ∨
      (Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi)) ∨
      ((Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi) ∨
      (Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi))) ∨
      (((¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0442 chi) ∨
      (Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0442 chi)) ∨
      ((Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0442 chi) ∨
      (Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0442 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0442 chi) ∨
      ((¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi))) ∨
      (((¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi)) ∨
      ((Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi)))) ∨
      ((((Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi)) ∨
      ((¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi))) ∨
      (((¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi)) ∨
      ((Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi))))) ∨
      (((((Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi)) ∨
      ((¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi))) ∨
      (((¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi)) ∨
      ((Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi)))) ∨
      ((((Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi)) ∨
      ((¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi))) ∨
      (((¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi)) ∨
      ((Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi)))))) ∨
      ((((((Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi)) ∨
      ((¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi))) ∨
      (((¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi)) ∨
      ((Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi)))) ∨
      ((((Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi)) ∨
      ((¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0448 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0448 chi))) ∨
      (((¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0448 chi) ∨
      (Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0448 chi)) ∨
      ((Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0448 chi) ∨
      (¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi))))) ∨
      (((((¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi)) ∨
      ((¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi))) ∨
      (((Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi)) ∨
      ((Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi)))) ∨
      ((((¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi)) ∨
      ((¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi))) ∨
      (((Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi)) ∨
      ((Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      ((¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi))) ∨
      (((Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi)) ∨
      ((Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi)))) ∨
      ((((¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi)) ∨
      ((¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi))) ∨
      (((Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi)) ∨
      ((Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi))))) ∨
      (((((¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi)) ∨
      ((¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi))) ∨
      (((Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi)) ∨
      ((Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi)))) ∨
      ((((¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi)) ∨
      ((¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi))) ∨
      (((Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi)) ∨
      ((Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi))) ∨
      (((Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi)))) ∨
      ((((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi))) ∨
      (((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi)) ∨
      ((Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi))))) ∨
      (((((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi))) ∨
      (((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi)) ∨
      ((Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi)))) ∨
      ((((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi))) ∨
      (((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi)) ∨
      ((Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi)))))))))) := by
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
                exact fin15Anchored_clause06057 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06058 chi hone hbad
                ·
                  exact fin15Anchored_clause06059 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06060 chi hone hbad
                ·
                  exact fin15Anchored_clause06061 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06062 chi hone hbad
                ·
                  exact fin15Anchored_clause06063 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06064 chi hone hbad
                ·
                  exact fin15Anchored_clause06065 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06066 chi hone hbad
                ·
                  exact fin15Anchored_clause06067 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06068 chi hone hbad
                ·
                  exact fin15Anchored_clause06069 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06070 chi hone hbad
                ·
                  exact fin15Anchored_clause06071 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06072 chi hone hbad
                ·
                  exact fin15Anchored_clause06073 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06074 chi hone hbad
                ·
                  exact fin15Anchored_clause06075 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06076 chi hone hbad
                ·
                  exact fin15Anchored_clause06077 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06078 chi hone hbad
                ·
                  exact fin15Anchored_clause06079 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06080 chi hone hbad
                ·
                  exact fin15Anchored_clause06081 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06082 chi hone hbad
                ·
                  exact fin15Anchored_clause06083 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06084 chi hone hbad
                ·
                  exact fin15Anchored_clause06085 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06086 chi hone hbad
                ·
                  exact fin15Anchored_clause06087 chi hone hbad
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
                  exact fin15Anchored_clause06088 chi hone hbad
                ·
                  exact fin15Anchored_clause06089 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06090 chi hone hbad
                ·
                  exact fin15Anchored_clause06091 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06092 chi hone hbad
                ·
                  exact fin15Anchored_clause06093 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06094 chi hone hbad
                ·
                  exact fin15Anchored_clause06095 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06096 chi hone hbad
                ·
                  exact fin15Anchored_clause06097 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06098 chi hone hbad
                ·
                  exact fin15Anchored_clause06099 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06100 chi hone hbad
                ·
                  exact fin15Anchored_clause06101 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06102 chi hone hbad
                ·
                  exact fin15Anchored_clause06103 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06104 chi hone hbad
                ·
                  exact fin15Anchored_clause06105 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06106 chi hone hbad
                ·
                  exact fin15Anchored_clause06107 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06108 chi hone hbad
                ·
                  exact fin15Anchored_clause06109 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06110 chi hone hbad
                ·
                  exact fin15Anchored_clause06111 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06112 chi hone hbad
                ·
                  exact fin15Anchored_clause06113 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06114 chi hone hbad
                ·
                  exact fin15Anchored_clause06115 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06116 chi hone hbad
                ·
                  exact fin15Anchored_clause06117 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06118 chi hone hbad
                ·
                  exact fin15Anchored_clause06119 chi hone hbad
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
                exact fin15Anchored_clause06120 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06121 chi hone hbad
                ·
                  exact fin15Anchored_clause06122 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06123 chi hone hbad
                ·
                  exact fin15Anchored_clause06124 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06125 chi hone hbad
                ·
                  exact fin15Anchored_clause06126 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06127 chi hone hbad
                ·
                  exact fin15Anchored_clause06128 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06129 chi hone hbad
                ·
                  exact fin15Anchored_clause06130 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06131 chi hone hbad
                ·
                  exact fin15Anchored_clause06132 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06133 chi hone hbad
                ·
                  exact fin15Anchored_clause06134 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06135 chi hone hbad
                ·
                  exact fin15Anchored_clause06136 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06137 chi hone hbad
                ·
                  exact fin15Anchored_clause06138 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06139 chi hone hbad
                ·
                  exact fin15Anchored_clause06140 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06141 chi hone hbad
                ·
                  exact fin15Anchored_clause06142 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06143 chi hone hbad
                ·
                  exact fin15Anchored_clause06144 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06145 chi hone hbad
                ·
                  exact fin15Anchored_clause06146 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06147 chi hone hbad
                ·
                  exact fin15Anchored_clause06148 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06149 chi hone hbad
                ·
                  exact fin15Anchored_clause06150 chi hone hbad
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
                  exact fin15Anchored_clause06151 chi hone hbad
                ·
                  exact fin15Anchored_clause06152 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06153 chi hone hbad
                ·
                  exact fin15Anchored_clause06154 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06155 chi hone hbad
                ·
                  exact fin15Anchored_clause06156 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06157 chi hone hbad
                ·
                  exact fin15Anchored_clause06158 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06159 chi hone hbad
                ·
                  exact fin15Anchored_clause06160 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06161 chi hone hbad
                ·
                  exact fin15Anchored_clause06162 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06163 chi hone hbad
                ·
                  exact fin15Anchored_clause06164 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06165 chi hone hbad
                ·
                  exact fin15Anchored_clause06166 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06167 chi hone hbad
                ·
                  exact fin15Anchored_clause06168 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06169 chi hone hbad
                ·
                  exact fin15Anchored_clause06170 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06171 chi hone hbad
                ·
                  exact fin15Anchored_clause06172 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06173 chi hone hbad
                ·
                  exact fin15Anchored_clause06174 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06175 chi hone hbad
                ·
                  exact fin15Anchored_clause06176 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06177 chi hone hbad
                ·
                  exact fin15Anchored_clause06178 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06179 chi hone hbad
                ·
                  exact fin15Anchored_clause06180 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06181 chi hone hbad
                ·
                  exact fin15Anchored_clause06182 chi hone hbad
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
                exact fin15Anchored_clause06183 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06184 chi hone hbad
                ·
                  exact fin15Anchored_clause06185 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06186 chi hone hbad
                ·
                  exact fin15Anchored_clause06187 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06188 chi hone hbad
                ·
                  exact fin15Anchored_clause06189 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06190 chi hone hbad
                ·
                  exact fin15Anchored_clause06191 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06192 chi hone hbad
                ·
                  exact fin15Anchored_clause06193 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06194 chi hone hbad
                ·
                  exact fin15Anchored_clause06195 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06196 chi hone hbad
                ·
                  exact fin15Anchored_clause06197 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06198 chi hone hbad
                ·
                  exact fin15Anchored_clause06199 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06200 chi hone hbad
                ·
                  exact fin15Anchored_clause06201 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06202 chi hone hbad
                ·
                  exact fin15Anchored_clause06203 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06204 chi hone hbad
                ·
                  exact fin15Anchored_clause06205 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06206 chi hone hbad
                ·
                  exact fin15Anchored_clause06207 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06208 chi hone hbad
                ·
                  exact fin15Anchored_clause06209 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06210 chi hone hbad
                ·
                  exact fin15Anchored_clause06211 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06212 chi hone hbad
                ·
                  exact fin15Anchored_clause06213 chi hone hbad
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
                  exact fin15Anchored_clause06214 chi hone hbad
                ·
                  exact fin15Anchored_clause06215 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06216 chi hone hbad
                ·
                  exact fin15Anchored_clause06217 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06218 chi hone hbad
                ·
                  exact fin15Anchored_clause06219 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06220 chi hone hbad
                ·
                  exact fin15Anchored_clause06221 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06222 chi hone hbad
                ·
                  exact fin15Anchored_clause06223 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06224 chi hone hbad
                ·
                  exact fin15Anchored_clause06225 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06226 chi hone hbad
                ·
                  exact fin15Anchored_clause06227 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06228 chi hone hbad
                ·
                  exact fin15Anchored_clause06229 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06230 chi hone hbad
                ·
                  exact fin15Anchored_clause06231 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06232 chi hone hbad
                ·
                  exact fin15Anchored_clause06233 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06234 chi hone hbad
                ·
                  exact fin15Anchored_clause06235 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06236 chi hone hbad
                ·
                  exact fin15Anchored_clause06237 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06238 chi hone hbad
                ·
                  exact fin15Anchored_clause06239 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06240 chi hone hbad
                ·
                  exact fin15Anchored_clause06241 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06242 chi hone hbad
                ·
                  exact fin15Anchored_clause06243 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06244 chi hone hbad
                ·
                  exact fin15Anchored_clause06245 chi hone hbad
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
                exact fin15Anchored_clause06246 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06247 chi hone hbad
                ·
                  exact fin15Anchored_clause06248 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06249 chi hone hbad
                ·
                  exact fin15Anchored_clause06250 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06251 chi hone hbad
                ·
                  exact fin15Anchored_clause06252 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06253 chi hone hbad
                ·
                  exact fin15Anchored_clause06254 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06255 chi hone hbad
                ·
                  exact fin15Anchored_clause06256 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06257 chi hone hbad
                ·
                  exact fin15Anchored_clause06258 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06259 chi hone hbad
                ·
                  exact fin15Anchored_clause06260 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06261 chi hone hbad
                ·
                  exact fin15Anchored_clause06262 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06263 chi hone hbad
                ·
                  exact fin15Anchored_clause06264 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06265 chi hone hbad
                ·
                  exact fin15Anchored_clause06266 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06267 chi hone hbad
                ·
                  exact fin15Anchored_clause06268 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06269 chi hone hbad
                ·
                  exact fin15Anchored_clause06270 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06271 chi hone hbad
                ·
                  exact fin15Anchored_clause06272 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06273 chi hone hbad
                ·
                  exact fin15Anchored_clause06274 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06275 chi hone hbad
                ·
                  exact fin15Anchored_clause06276 chi hone hbad
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
                  exact fin15Anchored_clause06277 chi hone hbad
                ·
                  exact fin15Anchored_clause06278 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06279 chi hone hbad
                ·
                  exact fin15Anchored_clause06280 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06281 chi hone hbad
                ·
                  exact fin15Anchored_clause06282 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06283 chi hone hbad
                ·
                  exact fin15Anchored_clause06284 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06285 chi hone hbad
                ·
                  exact fin15Anchored_clause06286 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06287 chi hone hbad
                ·
                  exact fin15Anchored_clause06288 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06289 chi hone hbad
                ·
                  exact fin15Anchored_clause06290 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06291 chi hone hbad
                ·
                  exact fin15Anchored_clause06292 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06293 chi hone hbad
                ·
                  exact fin15Anchored_clause06294 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06295 chi hone hbad
                ·
                  exact fin15Anchored_clause06296 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06297 chi hone hbad
                ·
                  exact fin15Anchored_clause06298 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06299 chi hone hbad
                ·
                  exact fin15Anchored_clause06300 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06301 chi hone hbad
                ·
                  exact fin15Anchored_clause06302 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06303 chi hone hbad
                ·
                  exact fin15Anchored_clause06304 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06305 chi hone hbad
                ·
                  exact fin15Anchored_clause06306 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06307 chi hone hbad
                ·
                  exact fin15Anchored_clause06308 chi hone hbad

end ErdosSzekeres

end
