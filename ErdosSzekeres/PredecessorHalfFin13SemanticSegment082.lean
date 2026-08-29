module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk062
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk063

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 082. -/

theorem predecessorHalfFin13_rejectSemanticSegment082
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) ∨
      ((PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) ∨
      (PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi))) ∨
      ((PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) ∨
      ((¬PredecessorHalfFin13Atom1221 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0726 chi) ∨
      (PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi)))) ∨
      (((PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) ∨
      ((PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) ∨
      (PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi))) ∨
      ((PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) ∨
      ((¬PredecessorHalfFin13Atom1222 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0727 chi) ∨
      (PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi))))) ∨
      ((((PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) ∨
      ((PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) ∨
      (PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi))) ∨
      ((PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) ∨
      ((¬PredecessorHalfFin13Atom1224 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0729 chi) ∨
      (PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi)))) ∨
      (((PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) ∨
      ((PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) ∨
      (PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi))) ∨
      ((PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) ∨
      ((¬PredecessorHalfFin13Atom1225 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0730 chi) ∨
      (PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) ∨
      ((PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) ∨
      (PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi))) ∨
      ((PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) ∨
      ((¬PredecessorHalfFin13Atom1227 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0732 chi) ∨
      (PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi)))) ∨
      (((PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) ∨
      ((PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) ∨
      (PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi))) ∨
      ((PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) ∨
      ((¬PredecessorHalfFin13Atom1229 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0734 chi) ∨
      (PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi))))) ∨
      ((((PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) ∨
      ((PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) ∨
      (PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi))) ∨
      ((PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) ∨
      ((¬PredecessorHalfFin13Atom1231 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0736 chi) ∨
      (PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi)))) ∨
      (((PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) ∨
      ((PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi) ∨
      (PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi))) ∨
      (((PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) ∨
      (¬PredecessorHalfFin13Atom1232 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0737 chi)) ∨
      ((PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) ∨
      (PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi) ∨
      ((PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) ∨
      (PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi))) ∨
      ((PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) ∨
      ((PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) ∨
      (PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi)))) ∨
      (((PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) ∨
      ((PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) ∨
      (PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi))) ∨
      ((PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) ∨
      ((PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi) ∨
      (PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi))))) ∨
      ((((PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) ∨
      ((PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) ∨
      (PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi))) ∨
      ((PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) ∨
      ((PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) ∨
      (PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1237 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0742 chi) ∨
      ((PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) ∨
      (PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi))) ∨
      ((PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi) ∨
      ((PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) ∨
      (PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) ∨
      ((PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) ∨
      (PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi))) ∨
      ((PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) ∨
      ((PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) ∨
      (PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi)))) ∨
      (((PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) ∨
      ((PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) ∨
      (PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi))) ∨
      ((PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) ∨
      ((¬PredecessorHalfFin13Atom1241 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0746 chi) ∨
      (PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi))))) ∨
      ((((PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) ∨
      ((PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) ∨
      (PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi))) ∨
      ((PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) ∨
      ((¬PredecessorHalfFin13Atom1242 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0747 chi) ∨
      (PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi)))) ∨
      (((PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) ∨
      ((PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) ∨
      (PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi))) ∨
      (((PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) ∨
      (¬PredecessorHalfFin13Atom1243 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0748 chi)) ∨
      ((PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) ∨
      (PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi))))))))) := by
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
              exact predecessorHalfFin13_clause18476 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18477 chi hbad
              ·
                exact predecessorHalfFin13_clause18478 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18479 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18480 chi hbad
              ·
                exact predecessorHalfFin13_clause18481 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18482 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18483 chi hbad
              ·
                exact predecessorHalfFin13_clause18484 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18485 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18486 chi hbad
              ·
                exact predecessorHalfFin13_clause18493 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18494 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18495 chi hbad
              ·
                exact predecessorHalfFin13_clause18496 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18497 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18498 chi hbad
              ·
                exact predecessorHalfFin13_clause18499 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18500 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18501 chi hbad
              ·
                exact predecessorHalfFin13_clause18502 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18503 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18504 chi hbad
              ·
                exact predecessorHalfFin13_clause18511 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18512 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18513 chi hbad
              ·
                exact predecessorHalfFin13_clause18514 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18515 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18516 chi hbad
              ·
                exact predecessorHalfFin13_clause18523 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18524 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18525 chi hbad
              ·
                exact predecessorHalfFin13_clause18526 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18527 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18528 chi hbad
              ·
                exact predecessorHalfFin13_clause18535 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18536 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18537 chi hbad
              ·
                exact predecessorHalfFin13_clause18538 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18539 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18540 chi hbad
              ·
                exact predecessorHalfFin13_clause18541 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18542 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18543 chi hbad
              ·
                exact predecessorHalfFin13_clause18544 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18545 chi hbad
              ·
                exact predecessorHalfFin13_clause18546 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18547 chi hbad
              ·
                exact predecessorHalfFin13_clause18548 chi hbad
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
              exact predecessorHalfFin13_clause18549 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18550 chi hbad
              ·
                exact predecessorHalfFin13_clause18551 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18553 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18554 chi hbad
              ·
                exact predecessorHalfFin13_clause18555 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18556 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18557 chi hbad
              ·
                exact predecessorHalfFin13_clause18565 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18566 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18567 chi hbad
              ·
                exact predecessorHalfFin13_clause18568 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18569 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18571 chi hbad
              ·
                exact predecessorHalfFin13_clause18572 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18573 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18574 chi hbad
              ·
                exact predecessorHalfFin13_clause18575 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18576 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18577 chi hbad
              ·
                exact predecessorHalfFin13_clause18578 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18579 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18580 chi hbad
              ·
                exact predecessorHalfFin13_clause18581 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18583 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18584 chi hbad
              ·
                exact predecessorHalfFin13_clause18585 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18586 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18587 chi hbad
              ·
                exact predecessorHalfFin13_clause18595 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18596 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18597 chi hbad
              ·
                exact predecessorHalfFin13_clause18598 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18599 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18600 chi hbad
              ·
                exact predecessorHalfFin13_clause18601 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18602 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18603 chi hbad
              ·
                exact predecessorHalfFin13_clause18604 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18605 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18606 chi hbad
              ·
                exact predecessorHalfFin13_clause18607 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18608 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18609 chi hbad
              ·
                exact predecessorHalfFin13_clause18610 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18611 chi hbad
              ·
                exact predecessorHalfFin13_clause18612 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18619 chi hbad
              ·
                exact predecessorHalfFin13_clause18620 chi hbad

end ErdosSzekeres

end
