module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk067
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk068

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 088. -/

theorem predecessorHalfFin13_rejectSemanticSegment088
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) ∨
      ((PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) ∨
      (PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi))) ∨
      ((PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) ∨
      ((PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) ∨
      (PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi)))) ∨
      (((PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) ∨
      ((PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) ∨
      (PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi))) ∨
      ((¬PredecessorHalfFin13Atom1377 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0882 chi) ∨
      ((PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) ∨
      (PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi))))) ∨
      ((((PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) ∨
      ((PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) ∨
      (PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi))) ∨
      ((¬PredecessorHalfFin13Atom1378 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0883 chi) ∨
      ((PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) ∨
      (PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi)))) ∨
      (((PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) ∨
      ((PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) ∨
      (PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi))) ∨
      ((PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) ∨
      ((PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) ∨
      (PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) ∨
      ((PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) ∨
      (¬PredecessorHalfFin13Atom1381 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0886 chi))) ∨
      ((PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) ∨
      ((PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) ∨
      (PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi)))) ∨
      (((PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) ∨
      ((PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) ∨
      (¬PredecessorHalfFin13Atom1382 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0887 chi))) ∨
      ((PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) ∨
      ((PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) ∨
      (PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi))))) ∨
      ((((PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) ∨
      ((PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) ∨
      (¬PredecessorHalfFin13Atom1383 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0888 chi))) ∨
      ((PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) ∨
      ((PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) ∨
      (PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi)))) ∨
      (((PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) ∨
      ((PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) ∨
      (¬PredecessorHalfFin13Atom1385 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0890 chi))) ∨
      (((PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) ∨
      (PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi)) ∨
      ((PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) ∨
      (PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) ∨
      ((¬PredecessorHalfFin13Atom1386 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0891 chi) ∨
      (PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi))) ∨
      ((PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) ∨
      ((PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) ∨
      (PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi)))) ∨
      (((PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) ∨
      ((¬PredecessorHalfFin13Atom1388 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0893 chi) ∨
      (PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi))) ∨
      ((PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) ∨
      ((PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) ∨
      (PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi))))) ∨
      ((((PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) ∨
      ((PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) ∨
      (PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi))) ∨
      ((PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) ∨
      ((PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) ∨
      (PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1392 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0897 chi) ∨
      ((PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) ∨
      (PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi))) ∨
      ((PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) ∨
      ((PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) ∨
      (PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1393 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0898 chi) ∨
      ((PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) ∨
      (PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi))) ∨
      ((PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) ∨
      ((PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) ∨
      (PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1394 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0899 chi) ∨
      ((PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) ∨
      (PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi))) ∨
      ((PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) ∨
      ((PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) ∨
      (PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1396 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0901 chi) ∨
      ((PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) ∨
      (PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi))) ∨
      ((PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) ∨
      ((PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) ∨
      (PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1397 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0902 chi) ∨
      ((PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) ∨
      (PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi))) ∨
      (((PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) ∨
      (PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi)) ∨
      ((PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) ∨
      (¬PredecessorHalfFin13Atom1398 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0903 chi))))))))) := by
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
              exact predecessorHalfFin13_clause19406 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19407 chi hbad
              ·
                exact predecessorHalfFin13_clause19408 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19409 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19411 chi hbad
              ·
                exact predecessorHalfFin13_clause19412 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19413 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19414 chi hbad
              ·
                exact predecessorHalfFin13_clause19415 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19416 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19417 chi hbad
              ·
                exact predecessorHalfFin13_clause19418 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19419 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19420 chi hbad
              ·
                exact predecessorHalfFin13_clause19421 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19422 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19423 chi hbad
              ·
                exact predecessorHalfFin13_clause19424 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19425 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19426 chi hbad
              ·
                exact predecessorHalfFin13_clause19427 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19435 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19436 chi hbad
              ·
                exact predecessorHalfFin13_clause19437 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19438 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19439 chi hbad
              ·
                exact predecessorHalfFin13_clause19440 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19441 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19442 chi hbad
              ·
                exact predecessorHalfFin13_clause19443 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19444 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19445 chi hbad
              ·
                exact predecessorHalfFin13_clause19446 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19447 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19448 chi hbad
              ·
                exact predecessorHalfFin13_clause19449 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19450 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19451 chi hbad
              ·
                exact predecessorHalfFin13_clause19452 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19459 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19460 chi hbad
              ·
                exact predecessorHalfFin13_clause19461 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19462 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19463 chi hbad
              ·
                exact predecessorHalfFin13_clause19464 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19465 chi hbad
              ·
                exact predecessorHalfFin13_clause19466 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19467 chi hbad
              ·
                exact predecessorHalfFin13_clause19468 chi hbad
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
              exact predecessorHalfFin13_clause19469 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19470 chi hbad
              ·
                exact predecessorHalfFin13_clause19477 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19478 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19479 chi hbad
              ·
                exact predecessorHalfFin13_clause19480 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19481 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19482 chi hbad
              ·
                exact predecessorHalfFin13_clause19489 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19490 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19491 chi hbad
              ·
                exact predecessorHalfFin13_clause19492 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19493 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19501 chi hbad
              ·
                exact predecessorHalfFin13_clause19502 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19503 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19504 chi hbad
              ·
                exact predecessorHalfFin13_clause19505 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19506 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19507 chi hbad
              ·
                exact predecessorHalfFin13_clause19508 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19509 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19510 chi hbad
              ·
                exact predecessorHalfFin13_clause19511 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19512 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19513 chi hbad
              ·
                exact predecessorHalfFin13_clause19514 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19515 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19516 chi hbad
              ·
                exact predecessorHalfFin13_clause19517 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19518 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19525 chi hbad
              ·
                exact predecessorHalfFin13_clause19526 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19527 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19528 chi hbad
              ·
                exact predecessorHalfFin13_clause19529 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19530 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19531 chi hbad
              ·
                exact predecessorHalfFin13_clause19532 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19533 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19534 chi hbad
              ·
                exact predecessorHalfFin13_clause19535 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19536 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19537 chi hbad
              ·
                exact predecessorHalfFin13_clause19538 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19539 chi hbad
              ·
                exact predecessorHalfFin13_clause19540 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19541 chi hbad
              ·
                exact predecessorHalfFin13_clause19542 chi hbad

end ErdosSzekeres

end
