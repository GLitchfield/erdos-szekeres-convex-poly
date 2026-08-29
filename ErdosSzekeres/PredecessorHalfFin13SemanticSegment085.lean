module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk065
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk066

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 085. -/

theorem predecessorHalfFin13_rejectSemanticSegment085
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) ∨
      ((¬PredecessorHalfFin13Atom1297 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0802 chi) ∨
      (PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi))) ∨
      ((PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) ∨
      ((PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) ∨
      (PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi)))) ∨
      (((PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) ∨
      ((¬PredecessorHalfFin13Atom1299 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0407 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0804 chi) ∨
      (PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi))) ∨
      ((PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) ∨
      ((PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) ∨
      (PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi))))) ∨
      ((((PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) ∨
      ((¬PredecessorHalfFin13Atom1300 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0805 chi) ∨
      (PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi))) ∨
      ((PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) ∨
      ((PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) ∨
      (PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi)))) ∨
      (((PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) ∨
      ((PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) ∨
      (PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi))) ∨
      ((PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) ∨
      ((PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) ∨
      (PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1302 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0807 chi) ∨
      ((PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) ∨
      (PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi))) ∨
      ((PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) ∨
      ((PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) ∨
      (PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1304 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0412 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0809 chi) ∨
      ((PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) ∨
      (PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi))) ∨
      ((PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom0413 chi) ∨
      ((PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) ∨
      (PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1305 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0413 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0810 chi) ∨
      ((PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) ∨
      (PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi))) ∨
      ((PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom0414 chi) ∨
      ((PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) ∨
      (PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1306 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0414 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0811 chi) ∨
      ((PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) ∨
      (PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi))) ∨
      (((PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom0416 chi) ∨
      (PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi)) ∨
      ((PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) ∨
      (¬PredecessorHalfFin13Atom1308 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0416 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0813 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) ∨
      ((PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) ∨
      (PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom0417 chi))) ∨
      ((PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) ∨
      ((PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) ∨
      (¬PredecessorHalfFin13Atom1309 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0417 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0814 chi)))) ∨
      (((PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) ∨
      ((PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) ∨
      (PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom0419 chi))) ∨
      ((PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) ∨
      ((PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) ∨
      (PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi))))) ∨
      ((((PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) ∨
      ((PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom0421 chi) ∨
      (PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi))) ∨
      ((PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) ∨
      ((¬PredecessorHalfFin13Atom1313 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0421 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0818 chi) ∨
      (PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi)))) ∨
      (((PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi) ∨
      ((PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) ∨
      (PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi))) ∨
      ((PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) ∨
      ((¬PredecessorHalfFin13Atom1315 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0820 chi) ∨
      (PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) ∨
      ((PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) ∨
      (PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi))) ∨
      ((PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) ∨
      ((¬PredecessorHalfFin13Atom1316 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0821 chi) ∨
      (PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi)))) ∨
      (((PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) ∨
      ((PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) ∨
      (PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi))) ∨
      ((PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) ∨
      ((¬PredecessorHalfFin13Atom1317 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0822 chi) ∨
      (PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi))))) ∨
      ((((PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) ∨
      ((PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) ∨
      (PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi))) ∨
      ((PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) ∨
      ((¬PredecessorHalfFin13Atom1318 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0823 chi) ∨
      (PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi)))) ∨
      (((PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) ∨
      ((PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) ∨
      (PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi))) ∨
      (((PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) ∨
      (PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi)) ∨
      ((PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) ∨
      (PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi))))))))) := by
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
              exact predecessorHalfFin13_clause18935 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18936 chi hbad
              ·
                exact predecessorHalfFin13_clause18943 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18944 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18945 chi hbad
              ·
                exact predecessorHalfFin13_clause18946 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18947 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18948 chi hbad
              ·
                exact predecessorHalfFin13_clause18949 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18950 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18951 chi hbad
              ·
                exact predecessorHalfFin13_clause18952 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18953 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18954 chi hbad
              ·
                exact predecessorHalfFin13_clause18955 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18956 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18957 chi hbad
              ·
                exact predecessorHalfFin13_clause18958 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18959 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18961 chi hbad
              ·
                exact predecessorHalfFin13_clause18962 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18963 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18964 chi hbad
              ·
                exact predecessorHalfFin13_clause18965 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18966 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18973 chi hbad
              ·
                exact predecessorHalfFin13_clause18974 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18975 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18976 chi hbad
              ·
                exact predecessorHalfFin13_clause18977 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18978 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18979 chi hbad
              ·
                exact predecessorHalfFin13_clause18980 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18981 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18982 chi hbad
              ·
                exact predecessorHalfFin13_clause18983 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18984 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18985 chi hbad
              ·
                exact predecessorHalfFin13_clause18986 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18987 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18988 chi hbad
              ·
                exact predecessorHalfFin13_clause18989 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18990 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18997 chi hbad
              ·
                exact predecessorHalfFin13_clause18998 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18999 chi hbad
              ·
                exact predecessorHalfFin13_clause19000 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19001 chi hbad
              ·
                exact predecessorHalfFin13_clause19002 chi hbad
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
              exact predecessorHalfFin13_clause19003 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19004 chi hbad
              ·
                exact predecessorHalfFin13_clause19005 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19006 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19007 chi hbad
              ·
                exact predecessorHalfFin13_clause19008 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19015 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19016 chi hbad
              ·
                exact predecessorHalfFin13_clause19017 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19018 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19019 chi hbad
              ·
                exact predecessorHalfFin13_clause19027 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19028 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19029 chi hbad
              ·
                exact predecessorHalfFin13_clause19030 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19031 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19032 chi hbad
              ·
                exact predecessorHalfFin13_clause19039 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19040 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19041 chi hbad
              ·
                exact predecessorHalfFin13_clause19042 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19043 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19044 chi hbad
              ·
                exact predecessorHalfFin13_clause19045 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19046 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19047 chi hbad
              ·
                exact predecessorHalfFin13_clause19048 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19049 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19050 chi hbad
              ·
                exact predecessorHalfFin13_clause19051 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19052 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19053 chi hbad
              ·
                exact predecessorHalfFin13_clause19054 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19055 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19056 chi hbad
              ·
                exact predecessorHalfFin13_clause19057 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19058 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19059 chi hbad
              ·
                exact predecessorHalfFin13_clause19060 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19061 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19062 chi hbad
              ·
                exact predecessorHalfFin13_clause19069 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19070 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19071 chi hbad
              ·
                exact predecessorHalfFin13_clause19072 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19073 chi hbad
              ·
                exact predecessorHalfFin13_clause19075 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19076 chi hbad
              ·
                exact predecessorHalfFin13_clause19077 chi hbad

end ErdosSzekeres

end
