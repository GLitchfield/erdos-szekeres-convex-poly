module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk066

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 086. -/

theorem predecessorHalfFin13_rejectSemanticSegment086
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) ∨
      ((PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) ∨
      (PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi))) ∨
      ((PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) ∨
      ((PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) ∨
      (PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi)))) ∨
      (((PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) ∨
      ((¬PredecessorHalfFin13Atom1322 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0827 chi) ∨
      (PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi))) ∨
      ((PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) ∨
      ((PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) ∨
      (PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi))))) ∨
      ((((PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) ∨
      ((¬PredecessorHalfFin13Atom1323 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0828 chi) ∨
      (PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi))) ∨
      ((PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) ∨
      ((PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) ∨
      (PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi)))) ∨
      (((PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) ∨
      ((PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) ∨
      (PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi))) ∨
      ((PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) ∨
      ((PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) ∨
      (PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1326 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0831 chi) ∨
      ((PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) ∨
      (PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi))) ∨
      ((PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) ∨
      ((PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) ∨
      (PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi)))) ∨
      (((PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) ∨
      ((PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) ∨
      (PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi))) ∨
      ((PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) ∨
      ((PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) ∨
      (PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi))))) ∨
      ((((PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) ∨
      ((PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) ∨
      (PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi))) ∨
      ((PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) ∨
      ((¬PredecessorHalfFin13Atom1330 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0835 chi) ∨
      (PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi)))) ∨
      (((PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) ∨
      ((PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi) ∨
      (PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi))) ∨
      (((PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) ∨
      (PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi)) ∨
      ((PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) ∨
      (PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) ∨
      ((PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) ∨
      (¬PredecessorHalfFin13Atom1334 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0839 chi))) ∨
      ((PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) ∨
      ((PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) ∨
      (PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi)))) ∨
      (((PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) ∨
      ((PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) ∨
      (¬PredecessorHalfFin13Atom1336 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0841 chi))) ∨
      ((PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) ∨
      ((PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) ∨
      (PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi))))) ∨
      ((((PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) ∨
      ((PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) ∨
      (¬PredecessorHalfFin13Atom1337 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0842 chi))) ∨
      ((PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) ∨
      ((PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) ∨
      (PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi)))) ∨
      (((PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) ∨
      ((PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) ∨
      (¬PredecessorHalfFin13Atom1338 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0843 chi))) ∨
      ((PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) ∨
      ((PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) ∨
      (PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) ∨
      ((PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) ∨
      (¬PredecessorHalfFin13Atom1340 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0845 chi))) ∨
      ((PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) ∨
      ((PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) ∨
      (PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi)))) ∨
      (((PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) ∨
      ((PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) ∨
      (¬PredecessorHalfFin13Atom1341 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0846 chi))) ∨
      ((PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) ∨
      ((PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) ∨
      (PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi))))) ∨
      ((((PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) ∨
      ((PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) ∨
      (¬PredecessorHalfFin13Atom1342 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0847 chi))) ∨
      ((PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) ∨
      ((PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) ∨
      (PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi)))) ∨
      (((PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) ∨
      ((PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) ∨
      (¬PredecessorHalfFin13Atom1344 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0849 chi))) ∨
      (((PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) ∨
      (PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi)) ∨
      ((PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi) ∨
      (PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi))))))))) := by
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
              exact predecessorHalfFin13_clause19078 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19079 chi hbad
              ·
                exact predecessorHalfFin13_clause19081 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19082 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19083 chi hbad
              ·
                exact predecessorHalfFin13_clause19084 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19085 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19086 chi hbad
              ·
                exact predecessorHalfFin13_clause19087 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19088 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19089 chi hbad
              ·
                exact predecessorHalfFin13_clause19090 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19091 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19092 chi hbad
              ·
                exact predecessorHalfFin13_clause19099 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19100 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19101 chi hbad
              ·
                exact predecessorHalfFin13_clause19102 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19103 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19105 chi hbad
              ·
                exact predecessorHalfFin13_clause19106 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19107 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19108 chi hbad
              ·
                exact predecessorHalfFin13_clause19109 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19110 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19111 chi hbad
              ·
                exact predecessorHalfFin13_clause19112 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19113 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19114 chi hbad
              ·
                exact predecessorHalfFin13_clause19115 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19123 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19124 chi hbad
              ·
                exact predecessorHalfFin13_clause19125 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19126 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19127 chi hbad
              ·
                exact predecessorHalfFin13_clause19129 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19130 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19131 chi hbad
              ·
                exact predecessorHalfFin13_clause19132 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19133 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19134 chi hbad
              ·
                exact predecessorHalfFin13_clause19141 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19142 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19143 chi hbad
              ·
                exact predecessorHalfFin13_clause19144 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19145 chi hbad
              ·
                exact predecessorHalfFin13_clause19153 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19154 chi hbad
              ·
                exact predecessorHalfFin13_clause19155 chi hbad
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
              exact predecessorHalfFin13_clause19156 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19157 chi hbad
              ·
                exact predecessorHalfFin13_clause19158 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19165 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19166 chi hbad
              ·
                exact predecessorHalfFin13_clause19167 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19168 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19169 chi hbad
              ·
                exact predecessorHalfFin13_clause19170 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19171 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19172 chi hbad
              ·
                exact predecessorHalfFin13_clause19173 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19174 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19175 chi hbad
              ·
                exact predecessorHalfFin13_clause19176 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19177 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19178 chi hbad
              ·
                exact predecessorHalfFin13_clause19179 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19180 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19181 chi hbad
              ·
                exact predecessorHalfFin13_clause19182 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19189 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19190 chi hbad
              ·
                exact predecessorHalfFin13_clause19191 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19192 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19193 chi hbad
              ·
                exact predecessorHalfFin13_clause19194 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19195 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19196 chi hbad
              ·
                exact predecessorHalfFin13_clause19197 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19198 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19199 chi hbad
              ·
                exact predecessorHalfFin13_clause19200 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19201 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19202 chi hbad
              ·
                exact predecessorHalfFin13_clause19203 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19204 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19205 chi hbad
              ·
                exact predecessorHalfFin13_clause19206 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19213 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19214 chi hbad
              ·
                exact predecessorHalfFin13_clause19215 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19216 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19217 chi hbad
              ·
                exact predecessorHalfFin13_clause19218 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19219 chi hbad
              ·
                exact predecessorHalfFin13_clause19220 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19221 chi hbad
              ·
                exact predecessorHalfFin13_clause19222 chi hbad

end ErdosSzekeres

end
