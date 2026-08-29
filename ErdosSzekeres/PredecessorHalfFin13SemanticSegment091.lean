module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk069
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk070

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 091. -/

theorem predecessorHalfFin13_rejectSemanticSegment091
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom1459 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0964 chi) ∨
      ((PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) ∨
      (PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi))) ∨
      ((PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) ∨
      ((PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) ∨
      (PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1462 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0967 chi) ∨
      ((PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) ∨
      (PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi))) ∨
      ((PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) ∨
      ((PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) ∨
      (PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1463 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0968 chi) ∨
      ((PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) ∨
      (PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi))) ∨
      ((PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) ∨
      ((PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) ∨
      (PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1465 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      ((PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) ∨
      (PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi))) ∨
      ((PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) ∨
      ((PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) ∨
      (PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) ∨
      ((PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) ∨
      (PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi))) ∨
      ((PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) ∨
      ((PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) ∨
      (¬PredecessorHalfFin13Atom1468 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0973 chi)))) ∨
      (((PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) ∨
      ((PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) ∨
      (PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi))) ∨
      ((PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) ∨
      ((PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) ∨
      (PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi))))) ∨
      ((((PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) ∨
      ((PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) ∨
      (PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi))) ∨
      ((PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) ∨
      ((PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) ∨
      (PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi)))) ∨
      (((PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) ∨
      ((PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) ∨
      (PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi))) ∨
      (((¬PredecessorHalfFin13Atom1474 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0979 chi) ∨
      (PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi)) ∨
      ((PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) ∨
      (PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) ∨
      ((PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) ∨
      (PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi))) ∨
      ((PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) ∨
      ((PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) ∨
      (PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi)))) ∨
      (((PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) ∨
      ((PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) ∨
      (PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi))) ∨
      ((PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) ∨
      ((PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) ∨
      (PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi))))) ∨
      ((((PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) ∨
      ((PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) ∨
      (PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi))) ∨
      ((PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) ∨
      ((PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) ∨
      (PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi)))) ∨
      (((PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) ∨
      ((PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) ∨
      (PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi))) ∨
      (((PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) ∨
      (¬PredecessorHalfFin13Atom1486 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0991 chi)) ∨
      ((PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) ∨
      (PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) ∨
      ((PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) ∨
      (PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi))) ∨
      ((¬PredecessorHalfFin13Atom1489 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0994 chi) ∨
      ((PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) ∨
      (PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi)))) ∨
      (((PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) ∨
      ((PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) ∨
      (PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi))) ∨
      ((PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) ∨
      ((PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) ∨
      (PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi))))) ∨
      ((((PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) ∨
      ((PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) ∨
      (¬PredecessorHalfFin13Atom1827 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0792 chi))) ∨
      ((PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) ∨
      ((PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) ∨
      (PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi)))) ∨
      (((PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi) ∨
      ((PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) ∨
      (¬PredecessorHalfFin13Atom1828 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0793 chi))) ∨
      (((PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) ∨
      (PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi)) ∨
      ((PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) ∨
      (PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi))))))))) := by
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
              exact predecessorHalfFin13_clause19908 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19921 chi hbad
              ·
                exact predecessorHalfFin13_clause19922 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19923 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19924 chi hbad
              ·
                exact predecessorHalfFin13_clause19925 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19926 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19927 chi hbad
              ·
                exact predecessorHalfFin13_clause19928 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19929 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19930 chi hbad
              ·
                exact predecessorHalfFin13_clause19931 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19932 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19939 chi hbad
              ·
                exact predecessorHalfFin13_clause19940 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19941 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19942 chi hbad
              ·
                exact predecessorHalfFin13_clause19943 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19944 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19945 chi hbad
              ·
                exact predecessorHalfFin13_clause19946 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19947 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19948 chi hbad
              ·
                exact predecessorHalfFin13_clause19949 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19957 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19958 chi hbad
              ·
                exact predecessorHalfFin13_clause19959 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19960 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19961 chi hbad
              ·
                exact predecessorHalfFin13_clause19962 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19969 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19970 chi hbad
              ·
                exact predecessorHalfFin13_clause19971 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19972 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19973 chi hbad
              ·
                exact predecessorHalfFin13_clause19981 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19982 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19983 chi hbad
              ·
                exact predecessorHalfFin13_clause19984 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19985 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19993 chi hbad
              ·
                exact predecessorHalfFin13_clause19994 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19995 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19996 chi hbad
              ·
                exact predecessorHalfFin13_clause19997 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19998 chi hbad
              ·
                exact predecessorHalfFin13_clause20005 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20006 chi hbad
              ·
                exact predecessorHalfFin13_clause20007 chi hbad
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
              exact predecessorHalfFin13_clause20008 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20009 chi hbad
              ·
                exact predecessorHalfFin13_clause20023 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause20024 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20025 chi hbad
              ·
                exact predecessorHalfFin13_clause20026 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause20027 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20041 chi hbad
              ·
                exact predecessorHalfFin13_clause20042 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause20043 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20044 chi hbad
              ·
                exact predecessorHalfFin13_clause20045 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause20053 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20054 chi hbad
              ·
                exact predecessorHalfFin13_clause20055 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause20056 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20057 chi hbad
              ·
                exact predecessorHalfFin13_clause20065 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause20066 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20067 chi hbad
              ·
                exact predecessorHalfFin13_clause20068 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20069 chi hbad
              ·
                exact predecessorHalfFin13_clause20070 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20083 chi hbad
              ·
                exact predecessorHalfFin13_clause20084 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause20085 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20086 chi hbad
              ·
                exact predecessorHalfFin13_clause20087 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause20088 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20107 chi hbad
              ·
                exact predecessorHalfFin13_clause20108 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause20109 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause20110 chi hbad
              ·
                exact predecessorHalfFin13_clause20111 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22111 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22112 chi hbad
              ·
                exact predecessorHalfFin13_clause22113 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22114 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22115 chi hbad
              ·
                exact predecessorHalfFin13_clause22116 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22117 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22118 chi hbad
              ·
                exact predecessorHalfFin13_clause22119 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause22120 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22121 chi hbad
              ·
                exact predecessorHalfFin13_clause22122 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22123 chi hbad
              ·
                exact predecessorHalfFin13_clause22124 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause22125 chi hbad
              ·
                exact predecessorHalfFin13_clause22126 chi hbad

end ErdosSzekeres

end
