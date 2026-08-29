module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk063
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk064

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 083. -/

theorem predecessorHalfFin13_rejectSemanticSegment083
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) ∨
      ((PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) ∨
      (PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi))) ∨
      ((¬PredecessorHalfFin13Atom1245 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0750 chi) ∨
      ((PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) ∨
      (PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi)))) ∨
      (((PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) ∨
      ((PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) ∨
      (PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi))) ∨
      ((¬PredecessorHalfFin13Atom1246 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0751 chi) ∨
      ((PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) ∨
      (PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi))))) ∨
      ((((PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) ∨
      ((PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) ∨
      (PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi))) ∨
      ((PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) ∨
      ((PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) ∨
      (PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi)))) ∨
      (((PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) ∨
      ((PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) ∨
      (¬PredecessorHalfFin13Atom1250 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0755 chi))) ∨
      ((PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) ∨
      ((PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi) ∨
      (PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) ∨
      ((PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) ∨
      (¬PredecessorHalfFin13Atom1252 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0757 chi))) ∨
      ((PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) ∨
      ((PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi) ∨
      (PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi)))) ∨
      (((PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) ∨
      ((PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) ∨
      (¬PredecessorHalfFin13Atom1253 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0758 chi))) ∨
      ((PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) ∨
      ((PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi) ∨
      (PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi))))) ∨
      ((((PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) ∨
      ((PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) ∨
      (¬PredecessorHalfFin13Atom1254 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0759 chi))) ∨
      ((PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) ∨
      ((PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi) ∨
      (PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi)))) ∨
      (((PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) ∨
      ((PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) ∨
      (¬PredecessorHalfFin13Atom1256 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0761 chi))) ∨
      (((PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi) ∨
      (PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi)) ∨
      ((PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) ∨
      (PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) ∨
      ((¬PredecessorHalfFin13Atom1257 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0762 chi) ∨
      (PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi))) ∨
      ((PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi) ∨
      ((PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) ∨
      (PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi)))) ∨
      (((PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) ∨
      ((¬PredecessorHalfFin13Atom1258 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0763 chi) ∨
      (PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi))) ∨
      ((PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi) ∨
      ((PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) ∨
      (PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi))))) ∨
      ((((PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) ∨
      ((¬PredecessorHalfFin13Atom1260 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0765 chi) ∨
      (PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi))) ∨
      ((PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi) ∨
      ((PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi) ∨
      (PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi)))) ∨
      (((PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) ∨
      ((¬PredecessorHalfFin13Atom1261 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0766 chi) ∨
      (PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi))) ∨
      (((PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi) ∨
      (PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi)) ∨
      ((PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) ∨
      (PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1263 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0768 chi) ∨
      ((PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi) ∨
      (PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi))) ∨
      ((PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) ∨
      ((PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) ∨
      (PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1265 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0770 chi) ∨
      ((PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) ∨
      (PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi))) ∨
      ((PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) ∨
      ((PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) ∨
      (PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1267 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0772 chi) ∨
      ((PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) ∨
      (PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi))) ∨
      ((PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) ∨
      ((PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) ∨
      (PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1268 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0773 chi) ∨
      ((PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) ∨
      (PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi))) ∨
      (((PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) ∨
      (PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi)) ∨
      ((PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) ∨
      (¬PredecessorHalfFin13Atom1270 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0775 chi))))))))) := by
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
              exact predecessorHalfFin13_clause18621 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18622 chi hbad
              ·
                exact predecessorHalfFin13_clause18623 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18624 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18625 chi hbad
              ·
                exact predecessorHalfFin13_clause18626 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18627 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18628 chi hbad
              ·
                exact predecessorHalfFin13_clause18629 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18630 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18637 chi hbad
              ·
                exact predecessorHalfFin13_clause18638 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18639 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18640 chi hbad
              ·
                exact predecessorHalfFin13_clause18641 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18649 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18650 chi hbad
              ·
                exact predecessorHalfFin13_clause18651 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18652 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18653 chi hbad
              ·
                exact predecessorHalfFin13_clause18654 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18661 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18662 chi hbad
              ·
                exact predecessorHalfFin13_clause18663 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18664 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18665 chi hbad
              ·
                exact predecessorHalfFin13_clause18666 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18667 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18668 chi hbad
              ·
                exact predecessorHalfFin13_clause18669 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18670 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18671 chi hbad
              ·
                exact predecessorHalfFin13_clause18672 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18673 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18674 chi hbad
              ·
                exact predecessorHalfFin13_clause18675 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18676 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18677 chi hbad
              ·
                exact predecessorHalfFin13_clause18678 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18685 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18686 chi hbad
              ·
                exact predecessorHalfFin13_clause18687 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18688 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18689 chi hbad
              ·
                exact predecessorHalfFin13_clause18690 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18691 chi hbad
              ·
                exact predecessorHalfFin13_clause18692 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18693 chi hbad
              ·
                exact predecessorHalfFin13_clause18694 chi hbad
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
              exact predecessorHalfFin13_clause18695 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18696 chi hbad
              ·
                exact predecessorHalfFin13_clause18697 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18698 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18699 chi hbad
              ·
                exact predecessorHalfFin13_clause18700 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18701 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18702 chi hbad
              ·
                exact predecessorHalfFin13_clause18709 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18710 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18711 chi hbad
              ·
                exact predecessorHalfFin13_clause18712 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18713 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18714 chi hbad
              ·
                exact predecessorHalfFin13_clause18715 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18716 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18717 chi hbad
              ·
                exact predecessorHalfFin13_clause18718 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18719 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18720 chi hbad
              ·
                exact predecessorHalfFin13_clause18727 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18728 chi hbad
              ·
                exact predecessorHalfFin13_clause18729 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18730 chi hbad
              ·
                exact predecessorHalfFin13_clause18731 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18732 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18739 chi hbad
              ·
                exact predecessorHalfFin13_clause18740 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18741 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18742 chi hbad
              ·
                exact predecessorHalfFin13_clause18743 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18744 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18751 chi hbad
              ·
                exact predecessorHalfFin13_clause18752 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18753 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18754 chi hbad
              ·
                exact predecessorHalfFin13_clause18755 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18756 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18757 chi hbad
              ·
                exact predecessorHalfFin13_clause18758 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18759 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18760 chi hbad
              ·
                exact predecessorHalfFin13_clause18761 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18762 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18769 chi hbad
              ·
                exact predecessorHalfFin13_clause18770 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18771 chi hbad
              ·
                exact predecessorHalfFin13_clause18772 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18773 chi hbad
              ·
                exact predecessorHalfFin13_clause18774 chi hbad

end ErdosSzekeres

end
