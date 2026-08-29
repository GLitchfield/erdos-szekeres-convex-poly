module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk066
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk067

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 087. -/

theorem predecessorHalfFin13_rejectSemanticSegment087
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) ∨
      ((¬PredecessorHalfFin13Atom1345 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0850 chi) ∨
      (PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi))) ∨
      ((PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) ∨
      ((PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) ∨
      (PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi)))) ∨
      (((PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) ∨
      ((¬PredecessorHalfFin13Atom1347 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0852 chi) ∨
      (PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi))) ∨
      ((PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) ∨
      ((PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) ∨
      (PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi))))) ∨
      ((((PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) ∨
      ((¬PredecessorHalfFin13Atom1349 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0854 chi) ∨
      (PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi))) ∨
      ((PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) ∨
      ((PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) ∨
      (PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi)))) ∨
      (((PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) ∨
      ((¬PredecessorHalfFin13Atom1351 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0856 chi) ∨
      (PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi))) ∨
      ((PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) ∨
      ((PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) ∨
      (PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) ∨
      ((¬PredecessorHalfFin13Atom1352 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0857 chi) ∨
      (PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi))) ∨
      ((PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) ∨
      ((PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi) ∨
      (PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi)))) ∨
      (((PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) ∨
      ((¬PredecessorHalfFin13Atom1354 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0859 chi) ∨
      (PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi))) ∨
      ((PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) ∨
      ((PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) ∨
      (PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi))))) ∨
      ((((PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) ∨
      ((¬PredecessorHalfFin13Atom1355 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0860 chi) ∨
      (PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi))) ∨
      ((PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) ∨
      ((PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) ∨
      (PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi)))) ∨
      (((PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) ∨
      ((¬PredecessorHalfFin13Atom1357 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0862 chi) ∨
      (PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi))) ∨
      (((PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) ∨
      (PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi)) ∨
      ((PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) ∨
      (PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom1359 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0864 chi) ∨
      ((PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) ∨
      (PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi))) ∨
      ((PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) ∨
      ((PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) ∨
      (PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1361 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0866 chi) ∨
      ((PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) ∨
      (PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi))) ∨
      ((PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) ∨
      ((PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) ∨
      (PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1363 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0868 chi) ∨
      ((PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) ∨
      (PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi))) ∨
      ((PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) ∨
      ((PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) ∨
      (PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1365 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0870 chi) ∨
      ((PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) ∨
      (PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi))) ∨
      (((PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) ∨
      (PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi)) ∨
      ((PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) ∨
      (¬PredecessorHalfFin13Atom1368 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0873 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) ∨
      ((PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) ∨
      (PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi))) ∨
      ((PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) ∨
      ((PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) ∨
      (¬PredecessorHalfFin13Atom1371 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0876 chi)))) ∨
      (((PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) ∨
      ((PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) ∨
      (PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi))) ∨
      ((PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) ∨
      ((PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) ∨
      (¬PredecessorHalfFin13Atom1372 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0877 chi))))) ∨
      ((((PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) ∨
      ((PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) ∨
      (PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi))) ∨
      ((PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) ∨
      ((PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) ∨
      (¬PredecessorHalfFin13Atom1373 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0878 chi)))) ∨
      (((PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) ∨
      ((PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) ∨
      (PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi))) ∨
      (((PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) ∨
      (PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi)) ∨
      ((¬PredecessorHalfFin13Atom1374 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0879 chi) ∨
      (PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi))))))))) := by
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
              exact predecessorHalfFin13_clause19223 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19224 chi hbad
              ·
                exact predecessorHalfFin13_clause19231 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19232 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19233 chi hbad
              ·
                exact predecessorHalfFin13_clause19234 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19235 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19236 chi hbad
              ·
                exact predecessorHalfFin13_clause19243 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19244 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19245 chi hbad
              ·
                exact predecessorHalfFin13_clause19246 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19247 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19248 chi hbad
              ·
                exact predecessorHalfFin13_clause19255 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19256 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19257 chi hbad
              ·
                exact predecessorHalfFin13_clause19258 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19259 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19260 chi hbad
              ·
                exact predecessorHalfFin13_clause19261 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19262 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19263 chi hbad
              ·
                exact predecessorHalfFin13_clause19264 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19265 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19266 chi hbad
              ·
                exact predecessorHalfFin13_clause19273 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19274 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19275 chi hbad
              ·
                exact predecessorHalfFin13_clause19276 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19277 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19278 chi hbad
              ·
                exact predecessorHalfFin13_clause19279 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19280 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19281 chi hbad
              ·
                exact predecessorHalfFin13_clause19282 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19283 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19284 chi hbad
              ·
                exact predecessorHalfFin13_clause19291 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19292 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19293 chi hbad
              ·
                exact predecessorHalfFin13_clause19294 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19295 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19296 chi hbad
              ·
                exact predecessorHalfFin13_clause19303 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19304 chi hbad
              ·
                exact predecessorHalfFin13_clause19305 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19306 chi hbad
              ·
                exact predecessorHalfFin13_clause19307 chi hbad
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
              exact predecessorHalfFin13_clause19308 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19315 chi hbad
              ·
                exact predecessorHalfFin13_clause19316 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19317 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19318 chi hbad
              ·
                exact predecessorHalfFin13_clause19319 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19320 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19327 chi hbad
              ·
                exact predecessorHalfFin13_clause19328 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19329 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19330 chi hbad
              ·
                exact predecessorHalfFin13_clause19331 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19332 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19339 chi hbad
              ·
                exact predecessorHalfFin13_clause19340 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19341 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19342 chi hbad
              ·
                exact predecessorHalfFin13_clause19343 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19344 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19357 chi hbad
              ·
                exact predecessorHalfFin13_clause19358 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19359 chi hbad
              ·
                exact predecessorHalfFin13_clause19360 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19361 chi hbad
              ·
                exact predecessorHalfFin13_clause19362 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19375 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19376 chi hbad
              ·
                exact predecessorHalfFin13_clause19377 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19378 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19379 chi hbad
              ·
                exact predecessorHalfFin13_clause19380 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19381 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19382 chi hbad
              ·
                exact predecessorHalfFin13_clause19383 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19384 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19385 chi hbad
              ·
                exact predecessorHalfFin13_clause19386 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19387 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19388 chi hbad
              ·
                exact predecessorHalfFin13_clause19389 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19390 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19391 chi hbad
              ·
                exact predecessorHalfFin13_clause19392 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19393 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19394 chi hbad
              ·
                exact predecessorHalfFin13_clause19395 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19396 chi hbad
              ·
                exact predecessorHalfFin13_clause19397 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19398 chi hbad
              ·
                exact predecessorHalfFin13_clause19405 chi hbad

end ErdosSzekeres

end
