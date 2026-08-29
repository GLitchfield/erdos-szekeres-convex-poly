module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk064
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk065

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 084. -/

theorem predecessorHalfFin13_rejectSemanticSegment084
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi) ∨
      ((PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) ∨
      (PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi))) ∨
      ((PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) ∨
      ((PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) ∨
      (¬PredecessorHalfFin13Atom1271 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0776 chi)))) ∨
      (((PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi) ∨
      ((PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) ∨
      (PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi))) ∨
      ((PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) ∨
      ((PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) ∨
      (¬PredecessorHalfFin13Atom1273 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0778 chi))))) ∨
      ((((PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) ∨
      ((PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) ∨
      (PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi))) ∨
      ((PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) ∨
      ((PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) ∨
      (¬PredecessorHalfFin13Atom1275 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0376 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0780 chi)))) ∨
      (((PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) ∨
      ((PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) ∨
      (PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi))) ∨
      ((PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) ∨
      ((PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) ∨
      (¬PredecessorHalfFin13Atom1277 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0378 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0497 chi ∧
      PredecessorHalfFin13Atom0782 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom0377 chi) ∨
      ((PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) ∨
      (PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi))) ∨
      ((PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) ∨
      ((PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) ∨
      (¬PredecessorHalfFin13Atom1279 chi ∧
      PredecessorHalfFin13Atom0377 chi ∧
      PredecessorHalfFin13Atom0380 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0784 chi)))) ∨
      (((PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom0378 chi) ∨
      ((PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom0380 chi) ∨
      (PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi))) ∨
      ((PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) ∨
      ((PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) ∨
      (PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom0381 chi))))) ∨
      ((((PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom0383 chi) ∨
      ((PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom0385 chi) ∨
      (PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi))) ∨
      ((PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) ∨
      ((¬PredecessorHalfFin13Atom1284 chi ∧
      PredecessorHalfFin13Atom0381 chi ∧
      PredecessorHalfFin13Atom0383 chi ∧
      PredecessorHalfFin13Atom0385 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0789 chi) ∨
      (PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi)))) ∨
      (((PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) ∨
      ((PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) ∨
      (PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom0423 chi))) ∨
      (((PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) ∨
      (PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi)) ∨
      ((PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) ∨
      (PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom0424 chi) ∨
      ((PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) ∨
      (¬PredecessorHalfFin13Atom1288 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0424 chi ∧
      PredecessorHalfFin13Atom0793 chi))) ∨
      ((PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) ∨
      ((PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) ∨
      (PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi)))) ∨
      (((PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom0425 chi) ∨
      ((PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) ∨
      (¬PredecessorHalfFin13Atom1289 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0425 chi ∧
      PredecessorHalfFin13Atom0794 chi))) ∨
      ((PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) ∨
      ((PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) ∨
      (PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi))))) ∨
      ((((PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom0426 chi) ∨
      ((PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) ∨
      (¬PredecessorHalfFin13Atom1290 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0398 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0795 chi))) ∨
      ((PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) ∨
      ((PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) ∨
      (PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi)))) ∨
      (((PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) ∨
      ((PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) ∨
      (¬PredecessorHalfFin13Atom1291 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0427 chi ∧
      PredecessorHalfFin13Atom0796 chi))) ∨
      ((PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) ∨
      ((PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) ∨
      (PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) ∨
      ((PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) ∨
      (¬PredecessorHalfFin13Atom1293 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0798 chi))) ∨
      ((PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) ∨
      ((PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) ∨
      (PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi)))) ∨
      (((PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) ∨
      ((PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) ∨
      (¬PredecessorHalfFin13Atom1294 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0799 chi))) ∨
      ((PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) ∨
      ((PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) ∨
      (PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi))))) ∨
      ((((PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) ∨
      ((PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) ∨
      (¬PredecessorHalfFin13Atom1295 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0390 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0800 chi))) ∨
      ((PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) ∨
      ((PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) ∨
      (PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi)))) ∨
      (((PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) ∨
      ((PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) ∨
      (¬PredecessorHalfFin13Atom1296 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0801 chi))) ∨
      (((PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) ∨
      (PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi)) ∨
      ((PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) ∨
      (PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi))))))))) := by
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
              exact predecessorHalfFin13_clause18775 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18776 chi hbad
              ·
                exact predecessorHalfFin13_clause18777 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18778 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18779 chi hbad
              ·
                exact predecessorHalfFin13_clause18780 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18787 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18788 chi hbad
              ·
                exact predecessorHalfFin13_clause18789 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18790 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18791 chi hbad
              ·
                exact predecessorHalfFin13_clause18792 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18799 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18800 chi hbad
              ·
                exact predecessorHalfFin13_clause18801 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18802 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18803 chi hbad
              ·
                exact predecessorHalfFin13_clause18804 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18811 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18812 chi hbad
              ·
                exact predecessorHalfFin13_clause18813 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18814 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18815 chi hbad
              ·
                exact predecessorHalfFin13_clause18816 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18823 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18824 chi hbad
              ·
                exact predecessorHalfFin13_clause18825 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18826 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18827 chi hbad
              ·
                exact predecessorHalfFin13_clause18828 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18835 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18836 chi hbad
              ·
                exact predecessorHalfFin13_clause18837 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18838 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18839 chi hbad
              ·
                exact predecessorHalfFin13_clause18853 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18854 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18855 chi hbad
              ·
                exact predecessorHalfFin13_clause18856 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18857 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18858 chi hbad
              ·
                exact predecessorHalfFin13_clause18871 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18872 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18873 chi hbad
              ·
                exact predecessorHalfFin13_clause18874 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18875 chi hbad
              ·
                exact predecessorHalfFin13_clause18877 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18878 chi hbad
              ·
                exact predecessorHalfFin13_clause18879 chi hbad
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
              exact predecessorHalfFin13_clause18880 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18881 chi hbad
              ·
                exact predecessorHalfFin13_clause18882 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18883 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18884 chi hbad
              ·
                exact predecessorHalfFin13_clause18885 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18886 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18887 chi hbad
              ·
                exact predecessorHalfFin13_clause18888 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18889 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18890 chi hbad
              ·
                exact predecessorHalfFin13_clause18891 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18892 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18893 chi hbad
              ·
                exact predecessorHalfFin13_clause18894 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18895 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18896 chi hbad
              ·
                exact predecessorHalfFin13_clause18897 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18898 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18899 chi hbad
              ·
                exact predecessorHalfFin13_clause18900 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18907 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18908 chi hbad
              ·
                exact predecessorHalfFin13_clause18909 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18910 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18911 chi hbad
              ·
                exact predecessorHalfFin13_clause18912 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18913 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18914 chi hbad
              ·
                exact predecessorHalfFin13_clause18915 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18916 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18917 chi hbad
              ·
                exact predecessorHalfFin13_clause18918 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18919 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18920 chi hbad
              ·
                exact predecessorHalfFin13_clause18921 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18922 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18923 chi hbad
              ·
                exact predecessorHalfFin13_clause18924 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18925 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18926 chi hbad
              ·
                exact predecessorHalfFin13_clause18927 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause18928 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18929 chi hbad
              ·
                exact predecessorHalfFin13_clause18930 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18931 chi hbad
              ·
                exact predecessorHalfFin13_clause18932 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause18933 chi hbad
              ·
                exact predecessorHalfFin13_clause18934 chi hbad

end ErdosSzekeres

end
