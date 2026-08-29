module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk062

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 081. -/

theorem predecessorHalfFin13_rejectSemanticSegment081
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom1199 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0419 chi ∧
      PredecessorHalfFin13Atom0704 chi) ∨
      ((PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) ∨
      (PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi))) ∨
      ((PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) ∨
      ((PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) ∨
      (PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1201 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0706 chi) ∨
      ((PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) ∨
      (PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi))) ∨
      ((PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) ∨
      ((PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi) ∨
      (PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1203 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0423 chi ∧
      PredecessorHalfFin13Atom0708 chi) ∨
      ((PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) ∨
      (PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi))) ∨
      ((PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) ∨
      ((PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) ∨
      (PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1204 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0709 chi) ∨
      ((PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) ∨
      (PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi))) ∨
      ((PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) ∨
      ((PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) ∨
      (PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1205 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0710 chi) ∨
      ((PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) ∨
      (PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi))) ∨
      ((PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) ∨
      ((PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) ∨
      (PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1206 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0362 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0711 chi) ∨
      ((PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) ∨
      (PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi))) ∨
      ((PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) ∨
      ((PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) ∨
      (PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1207 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0712 chi) ∨
      ((PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) ∨
      (PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi))) ∨
      ((PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) ∨
      ((PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) ∨
      (PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1209 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0714 chi) ∨
      ((PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) ∨
      (PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi))) ∨
      (((PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) ∨
      (PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi)) ∨
      ((PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) ∨
      (¬PredecessorHalfFin13Atom1210 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0715 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) ∨
      ((PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) ∨
      (PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi))) ∨
      ((PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) ∨
      ((PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) ∨
      (¬PredecessorHalfFin13Atom1211 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0716 chi)))) ∨
      (((PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) ∨
      ((PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) ∨
      (PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi))) ∨
      ((PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) ∨
      ((PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) ∨
      (¬PredecessorHalfFin13Atom1212 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0717 chi))))) ∨
      ((((PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) ∨
      ((PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) ∨
      (PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi))) ∨
      ((PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) ∨
      ((PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) ∨
      (¬PredecessorHalfFin13Atom1213 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0718 chi)))) ∨
      (((PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) ∨
      ((PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) ∨
      (PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi))) ∨
      ((PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) ∨
      ((PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) ∨
      (¬PredecessorHalfFin13Atom1215 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0371 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0720 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) ∨
      ((PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) ∨
      (PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi))) ∨
      ((PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) ∨
      ((PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) ∨
      (¬PredecessorHalfFin13Atom1216 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0354 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0721 chi)))) ∨
      (((PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) ∨
      ((PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) ∨
      (PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi))) ∨
      ((PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) ∨
      ((PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) ∨
      (¬PredecessorHalfFin13Atom1217 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0722 chi))))) ∨
      ((((PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) ∨
      ((PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) ∨
      (PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi))) ∨
      ((PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) ∨
      ((PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) ∨
      (¬PredecessorHalfFin13Atom1218 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0723 chi)))) ∨
      (((PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) ∨
      ((PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) ∨
      (PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi))) ∨
      (((PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) ∨
      (PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi)) ∨
      ((¬PredecessorHalfFin13Atom1220 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0725 chi) ∨
      (PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi))))))))) := by
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
              exact predecessorHalfFin13_clause18348 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18355 chi hbad
              ·
                exact predecessorHalfFin13_clause18356 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18357 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18358 chi hbad
              ·
                exact predecessorHalfFin13_clause18359 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18360 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18367 chi hbad
              ·
                exact predecessorHalfFin13_clause18368 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18369 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18370 chi hbad
              ·
                exact predecessorHalfFin13_clause18371 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18372 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18373 chi hbad
              ·
                exact predecessorHalfFin13_clause18374 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18375 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18376 chi hbad
              ·
                exact predecessorHalfFin13_clause18377 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18378 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18379 chi hbad
              ·
                exact predecessorHalfFin13_clause18380 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18381 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18382 chi hbad
              ·
                exact predecessorHalfFin13_clause18383 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18384 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18385 chi hbad
              ·
                exact predecessorHalfFin13_clause18386 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18387 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18388 chi hbad
              ·
                exact predecessorHalfFin13_clause18389 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18390 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18391 chi hbad
              ·
                exact predecessorHalfFin13_clause18392 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18393 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18394 chi hbad
              ·
                exact predecessorHalfFin13_clause18395 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18396 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18403 chi hbad
              ·
                exact predecessorHalfFin13_clause18404 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18405 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18406 chi hbad
              ·
                exact predecessorHalfFin13_clause18407 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18408 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18409 chi hbad
              ·
                exact predecessorHalfFin13_clause18410 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18411 chi hbad
              ·
                exact predecessorHalfFin13_clause18412 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18413 chi hbad
              ·
                exact predecessorHalfFin13_clause18414 chi hbad
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
              exact predecessorHalfFin13_clause18415 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18416 chi hbad
              ·
                exact predecessorHalfFin13_clause18417 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18418 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18419 chi hbad
              ·
                exact predecessorHalfFin13_clause18420 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18421 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18422 chi hbad
              ·
                exact predecessorHalfFin13_clause18423 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18424 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18425 chi hbad
              ·
                exact predecessorHalfFin13_clause18426 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18427 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18428 chi hbad
              ·
                exact predecessorHalfFin13_clause18429 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18430 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18431 chi hbad
              ·
                exact predecessorHalfFin13_clause18432 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18439 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18440 chi hbad
              ·
                exact predecessorHalfFin13_clause18441 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18442 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18443 chi hbad
              ·
                exact predecessorHalfFin13_clause18444 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18445 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18446 chi hbad
              ·
                exact predecessorHalfFin13_clause18447 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18448 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18449 chi hbad
              ·
                exact predecessorHalfFin13_clause18450 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18451 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18452 chi hbad
              ·
                exact predecessorHalfFin13_clause18453 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18454 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18455 chi hbad
              ·
                exact predecessorHalfFin13_clause18456 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18457 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18458 chi hbad
              ·
                exact predecessorHalfFin13_clause18459 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18460 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18461 chi hbad
              ·
                exact predecessorHalfFin13_clause18462 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18469 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18470 chi hbad
              ·
                exact predecessorHalfFin13_clause18471 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18472 chi hbad
              ·
                exact predecessorHalfFin13_clause18473 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18474 chi hbad
              ·
                exact predecessorHalfFin13_clause18475 chi hbad

end ErdosSzekeres

end
