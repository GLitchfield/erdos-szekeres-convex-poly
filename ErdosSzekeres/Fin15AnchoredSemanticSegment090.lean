module

public import ErdosSzekeres.Fin15AnchoredClauseChunk177
public import ErdosSzekeres.Fin15AnchoredClauseChunk178
public import ErdosSzekeres.Fin15AnchoredClauseChunk179

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 090. -/

theorem fin15Anchored_rejectSemanticSegment090
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom1009 chi) ∨
      ((Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom1073 chi) ∨
      (Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom1662 chi))) ∨
      (((¬Fin15AnchoredAtom3378 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1662 chi) ∨
      (Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom1001 chi)) ∨
      ((Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom1005 chi) ∨
      (Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom1010 chi)))) ∨
      ((((Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom1663 chi) ∨
      (¬Fin15AnchoredAtom3379 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1663 chi)) ∨
      ((Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom1001 chi) ∨
      (Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom1006 chi))) ∨
      (((Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom1011 chi) ∨
      (Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom1075 chi)) ∨
      ((Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom1664 chi) ∨
      (Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom1002 chi))))) ∨
      (((((Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom1004 chi) ∨
      (Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom1013 chi)) ∨
      ((Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom1666 chi) ∨
      (¬Fin15AnchoredAtom3382 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1666 chi))) ∨
      (((Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom1002 chi) ∨
      (Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom1005 chi)) ∨
      ((Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom1014 chi) ∨
      (Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom1078 chi)))) ∨
      ((((Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom1667 chi) ∨
      (¬Fin15AnchoredAtom3383 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1667 chi)) ∨
      ((Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom1002 chi) ∨
      (Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom1015 chi))) ∨
      (((Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom1079 chi) ∨
      (Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom1668 chi)) ∨
      ((Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom1005 chi) ∨
      (Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom1019 chi)))))) ∨
      ((((((Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom1672 chi) ∨
      (¬Fin15AnchoredAtom3388 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1672 chi)) ∨
      ((Fin15AnchoredAtom3389 chi ∧
      ¬Fin15AnchoredAtom1006 chi) ∨
      (Fin15AnchoredAtom3389 chi ∧
      ¬Fin15AnchoredAtom1020 chi))) ∨
      (((Fin15AnchoredAtom3389 chi ∧
      ¬Fin15AnchoredAtom1673 chi) ∨
      (¬Fin15AnchoredAtom3389 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1006 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1673 chi)) ∨
      ((Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom1005 chi) ∨
      (Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom1006 chi)))) ∨
      ((((Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom1021 chi) ∨
      (Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom1674 chi)) ∨
      ((¬Fin15AnchoredAtom3390 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1006 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1674 chi) ∨
      (Fin15AnchoredAtom3391 chi ∧
      ¬Fin15AnchoredAtom1007 chi))) ∨
      (((Fin15AnchoredAtom3391 chi ∧
      ¬Fin15AnchoredAtom1008 chi) ∨
      (Fin15AnchoredAtom3391 chi ∧
      ¬Fin15AnchoredAtom1675 chi)) ∨
      ((Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom1009 chi))))) ∨
      (((((Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom1013 chi) ∨
      (Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom1087 chi)) ∨
      ((Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom1676 chi) ∨
      (¬Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1676 chi))) ∨
      (((Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom1010 chi)) ∨
      ((Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom1014 chi) ∨
      (Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom1088 chi)))) ∨
      ((((Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom1677 chi) ∨
      (¬Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1677 chi)) ∨
      ((Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom1011 chi))) ∨
      (((Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom1015 chi) ∨
      (Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom1089 chi)) ∨
      ((Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom1678 chi) ∨
      (¬Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1678 chi))))))) ∨
      ((((((Fin15AnchoredAtom3395 chi ∧
      ¬Fin15AnchoredAtom1008 chi) ∨
      ((Fin15AnchoredAtom3395 chi ∧
      ¬Fin15AnchoredAtom1009 chi) ∨
      (Fin15AnchoredAtom3395 chi ∧
      ¬Fin15AnchoredAtom1679 chi))) ∨
      (((Fin15AnchoredAtom3396 chi ∧
      ¬Fin15AnchoredAtom1010 chi) ∨
      (Fin15AnchoredAtom3397 chi ∧
      ¬Fin15AnchoredAtom1011 chi)) ∨
      ((Fin15AnchoredAtom3397 chi ∧
      ¬Fin15AnchoredAtom1681 chi) ∨
      (Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom1009 chi)))) ∨
      ((((Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom1010 chi) ∨
      (Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom1019 chi)) ∨
      ((Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom1093 chi) ∨
      (Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom1682 chi))) ∨
      (((¬Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1682 chi) ∨
      (Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom1009 chi)) ∨
      ((Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom1011 chi) ∨
      (Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom1020 chi))))) ∨
      (((((Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom1094 chi) ∨
      (Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom1683 chi)) ∨
      ((¬Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1683 chi) ∨
      (Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom1010 chi))) ∨
      (((Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom1011 chi) ∨
      (Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom1021 chi)) ∨
      ((Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom1095 chi) ∨
      (Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom1684 chi)))) ∨
      ((((¬Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1684 chi) ∨
      (Fin15AnchoredAtom3401 chi ∧
      ¬Fin15AnchoredAtom1096 chi)) ∨
      ((¬Fin15AnchoredAtom3402 chi ∧
      Fin15AnchoredAtom1012 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1017 chi ∧
      Fin15AnchoredAtom1097 chi ∧
      Fin15AnchoredAtom1686 chi) ∨
      (Fin15AnchoredAtom3403 chi ∧
      ¬Fin15AnchoredAtom1015 chi))) ∨
      (((Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom1013 chi) ∨
      (Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom1014 chi)) ∨
      ((Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom1019 chi) ∨
      (Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom1099 chi)))))) ∨
      ((((((Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (¬Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1688 chi)) ∨
      ((Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom1013 chi) ∨
      (Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom1015 chi))) ∨
      (((Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom1020 chi) ∨
      (Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom1100 chi)) ∨
      ((Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom1689 chi) ∨
      (¬Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1689 chi)))) ∨
      ((((Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom1014 chi) ∨
      (Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom1015 chi)) ∨
      ((Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom1021 chi) ∨
      (Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom1101 chi))) ∨
      (((Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom1690 chi) ∨
      (¬Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1690 chi)) ∨
      ((Fin15AnchoredAtom3407 chi ∧
      ¬Fin15AnchoredAtom1019 chi) ∨
      (Fin15AnchoredAtom3408 chi ∧
      ¬Fin15AnchoredAtom1020 chi))))) ∨
      (((((Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom1019 chi) ∨
      (Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom1020 chi)) ∨
      ((Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom1021 chi) ∨
      (Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom1105 chi))) ∨
      (((Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom1694 chi) ∨
      (¬Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1694 chi)) ∨
      ((Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom1022 chi) ∨
      (Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom1023 chi)))) ∨
      ((((Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom1029 chi) ∨
      (Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom1050 chi)) ∨
      ((Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom1695 chi) ∨
      (¬Fin15AnchoredAtom3411 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1695 chi))) ∨
      (((Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom1022 chi) ∨
      (Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom1024 chi)) ∨
      ((Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom1030 chi) ∨
      (Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom1051 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom1696 chi) ∨
      ((¬Fin15AnchoredAtom3412 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1696 chi) ∨
      (Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom1022 chi))) ∨
      (((Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom1026 chi) ∨
      (Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom1032 chi)) ∨
      ((Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (¬Fin15AnchoredAtom3414 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1698 chi)))) ∨
      ((((Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom1022 chi) ∨
      (Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom1027 chi)) ∨
      ((Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom1033 chi) ∨
      (Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom1054 chi))) ∨
      (((Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom1699 chi) ∨
      (¬Fin15AnchoredAtom3415 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1699 chi)) ∨
      ((Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom1022 chi) ∨
      (Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom1028 chi))))) ∨
      (((((Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom1034 chi) ∨
      (Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom1055 chi)) ∨
      ((¬Fin15AnchoredAtom3416 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1034 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1700 chi) ∨
      (Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom1023 chi))) ∨
      (((Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom1024 chi) ∨
      (Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom1035 chi)) ∨
      ((Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom1701 chi)))) ∨
      ((((¬Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1701 chi) ∨
      (Fin15AnchoredAtom3418 chi ∧
      ¬Fin15AnchoredAtom1025 chi)) ∨
      ((Fin15AnchoredAtom3418 chi ∧
      ¬Fin15AnchoredAtom1057 chi) ∨
      (Fin15AnchoredAtom3418 chi ∧
      ¬Fin15AnchoredAtom1702 chi))) ∨
      (((Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom1023 chi) ∨
      (Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom1026 chi)) ∨
      ((Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom1058 chi)))))) ∨
      ((((((Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom1703 chi) ∨
      (¬Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1703 chi)) ∨
      ((Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom1023 chi) ∨
      (Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom1027 chi))) ∨
      (((Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom1038 chi) ∨
      (Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom1059 chi)) ∨
      ((Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom1704 chi) ∨
      (¬Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1704 chi)))) ∨
      ((((Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom1023 chi) ∨
      (Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom1028 chi)) ∨
      ((Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom1039 chi) ∨
      (Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom1060 chi))) ∨
      (((Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom1705 chi) ∨
      (¬Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1705 chi)) ∨
      ((Fin15AnchoredAtom3422 chi ∧
      ¬Fin15AnchoredAtom1024 chi) ∨
      (Fin15AnchoredAtom3422 chi ∧
      ¬Fin15AnchoredAtom1040 chi))))) ∨
      (((((Fin15AnchoredAtom3422 chi ∧
      ¬Fin15AnchoredAtom1706 chi) ∨
      (Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom1024 chi)) ∨
      ((Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom1026 chi) ∨
      (Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom1041 chi))) ∨
      (((Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom1062 chi) ∨
      (Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom1707 chi)) ∨
      ((¬Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1707 chi) ∨
      (Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom1024 chi)))) ∨
      ((((Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom1027 chi) ∨
      (Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom1042 chi)) ∨
      ((Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom1063 chi) ∨
      (Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom1708 chi))) ∨
      (((¬Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1708 chi) ∨
      (Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom1024 chi)) ∨
      ((Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom1028 chi) ∨
      (Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom1043 chi))))))) ∨
      ((((((Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom1064 chi) ∨
      ((Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom1709 chi) ∨
      (¬Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1709 chi))) ∨
      (((Fin15AnchoredAtom3426 chi ∧
      ¬Fin15AnchoredAtom1026 chi) ∨
      (Fin15AnchoredAtom3426 chi ∧
      ¬Fin15AnchoredAtom1065 chi)) ∨
      ((Fin15AnchoredAtom3426 chi ∧
      ¬Fin15AnchoredAtom1710 chi) ∨
      (Fin15AnchoredAtom3428 chi ∧
      ¬Fin15AnchoredAtom1712 chi)))) ∨
      ((((Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom1026 chi) ∨
      (Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom1027 chi)) ∨
      ((Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom1047 chi) ∨
      (Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom1068 chi))) ∨
      (((Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom1713 chi) ∨
      (¬Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1713 chi)) ∨
      ((Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom1026 chi) ∨
      (Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom1028 chi))))) ∨
      (((((Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom1048 chi) ∨
      (Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom1069 chi)) ∨
      ((Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom1714 chi) ∨
      (¬Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1714 chi))) ∨
      (((Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom1027 chi) ∨
      (Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom1028 chi)) ∨
      ((Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom1049 chi) ∨
      (Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom1070 chi)))) ∨
      ((((Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom1715 chi) ∨
      (¬Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1715 chi)) ∨
      ((Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom1029 chi) ∨
      (Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom1030 chi))) ∨
      (((Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom1035 chi) ∨
      (Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom1071 chi)) ∨
      ((Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom1716 chi) ∨
      (¬Fin15AnchoredAtom3432 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1716 chi)))))) ∨
      ((((((Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom1029 chi) ∨
      (Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom1032 chi)) ∨
      ((Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom1073 chi))) ∨
      (((Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom1718 chi) ∨
      (¬Fin15AnchoredAtom3434 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1718 chi)) ∨
      ((Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom1029 chi) ∨
      (Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom1033 chi)))) ∨
      ((((Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom1038 chi) ∨
      (Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom1074 chi)) ∨
      ((Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom1719 chi) ∨
      (¬Fin15AnchoredAtom3435 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1719 chi))) ∨
      (((Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom1029 chi) ∨
      (Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom1034 chi)) ∨
      ((Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom1039 chi) ∨
      (Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom1720 chi))))) ∨
      (((((Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom1030 chi) ∨
      (Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom1032 chi)) ∨
      ((Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom1041 chi) ∨
      (Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom1722 chi))) ∨
      (((¬Fin15AnchoredAtom3438 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1722 chi) ∨
      (Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom1030 chi)) ∨
      ((Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom1033 chi) ∨
      (Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom1042 chi)))) ∨
      ((((Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom1078 chi) ∨
      (Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom1723 chi)) ∨
      ((¬Fin15AnchoredAtom3439 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1723 chi) ∨
      (Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom1030 chi))) ∨
      (((Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom1034 chi) ∨
      (Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom1043 chi)) ∨
      ((Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom1079 chi) ∨
      (Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom1724 chi)))))))))) := by
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
                exact fin15Anchored_clause22716 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22717 chi hbad
                ·
                  exact fin15Anchored_clause22718 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22719 chi hbad
                ·
                  exact fin15Anchored_clause22720 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22721 chi hbad
                ·
                  exact fin15Anchored_clause22722 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22723 chi hbad
                ·
                  exact fin15Anchored_clause22724 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22725 chi hbad
                ·
                  exact fin15Anchored_clause22726 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22727 chi hbad
                ·
                  exact fin15Anchored_clause22728 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22729 chi hbad
                ·
                  exact fin15Anchored_clause22730 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22731 chi hbad
                ·
                  exact fin15Anchored_clause22732 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22733 chi hbad
                ·
                  exact fin15Anchored_clause22734 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22735 chi hbad
                ·
                  exact fin15Anchored_clause22736 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22737 chi hbad
                ·
                  exact fin15Anchored_clause22738 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22739 chi hbad
                ·
                  exact fin15Anchored_clause22740 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22741 chi hbad
                ·
                  exact fin15Anchored_clause22742 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22743 chi hbad
                ·
                  exact fin15Anchored_clause22744 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22745 chi hbad
                ·
                  exact fin15Anchored_clause22746 chi hbad
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
                  exact fin15Anchored_clause22747 chi hbad
                ·
                  exact fin15Anchored_clause22748 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22749 chi hbad
                ·
                  exact fin15Anchored_clause22750 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22751 chi hbad
                ·
                  exact fin15Anchored_clause22752 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22753 chi hbad
                ·
                  exact fin15Anchored_clause22754 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22755 chi hbad
                ·
                  exact fin15Anchored_clause22756 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22757 chi hbad
                ·
                  exact fin15Anchored_clause22758 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22759 chi hbad
                ·
                  exact fin15Anchored_clause22760 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22761 chi hbad
                ·
                  exact fin15Anchored_clause22762 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22763 chi hbad
                ·
                  exact fin15Anchored_clause22764 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22765 chi hbad
                ·
                  exact fin15Anchored_clause22766 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22767 chi hbad
                ·
                  exact fin15Anchored_clause22768 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22769 chi hbad
                ·
                  exact fin15Anchored_clause22770 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22771 chi hbad
                ·
                  exact fin15Anchored_clause22772 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22773 chi hbad
                ·
                  exact fin15Anchored_clause22774 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22775 chi hbad
                ·
                  exact fin15Anchored_clause22776 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22777 chi hbad
                ·
                  exact fin15Anchored_clause22778 chi hbad
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
                exact fin15Anchored_clause22779 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22780 chi hbad
                ·
                  exact fin15Anchored_clause22781 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22782 chi hbad
                ·
                  exact fin15Anchored_clause22783 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22784 chi hbad
                ·
                  exact fin15Anchored_clause22785 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22786 chi hbad
                ·
                  exact fin15Anchored_clause22787 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22788 chi hbad
                ·
                  exact fin15Anchored_clause22789 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22790 chi hbad
                ·
                  exact fin15Anchored_clause22791 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22792 chi hbad
                ·
                  exact fin15Anchored_clause22793 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22794 chi hbad
                ·
                  exact fin15Anchored_clause22795 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22796 chi hbad
                ·
                  exact fin15Anchored_clause22797 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22798 chi hbad
                ·
                  exact fin15Anchored_clause22799 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22800 chi hbad
                ·
                  exact fin15Anchored_clause22801 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22802 chi hbad
                ·
                  exact fin15Anchored_clause22803 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22804 chi hbad
                ·
                  exact fin15Anchored_clause22805 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22806 chi hbad
                ·
                  exact fin15Anchored_clause22807 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22808 chi hbad
                ·
                  exact fin15Anchored_clause22809 chi hbad
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
                  exact fin15Anchored_clause22810 chi hbad
                ·
                  exact fin15Anchored_clause22811 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22812 chi hbad
                ·
                  exact fin15Anchored_clause22813 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22814 chi hbad
                ·
                  exact fin15Anchored_clause22815 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22816 chi hbad
                ·
                  exact fin15Anchored_clause22817 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22818 chi hbad
                ·
                  exact fin15Anchored_clause22819 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22820 chi hbad
                ·
                  exact fin15Anchored_clause22821 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22822 chi hbad
                ·
                  exact fin15Anchored_clause22823 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22824 chi hbad
                ·
                  exact fin15Anchored_clause22825 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22826 chi hbad
                ·
                  exact fin15Anchored_clause22827 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22828 chi hbad
                ·
                  exact fin15Anchored_clause22829 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22830 chi hbad
                ·
                  exact fin15Anchored_clause22831 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22832 chi hbad
                ·
                  exact fin15Anchored_clause22833 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22834 chi hbad
                ·
                  exact fin15Anchored_clause22835 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22836 chi hbad
                ·
                  exact fin15Anchored_clause22837 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22838 chi hbad
                ·
                  exact fin15Anchored_clause22839 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22840 chi hbad
                ·
                  exact fin15Anchored_clause22841 chi hbad
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
                exact fin15Anchored_clause22842 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22843 chi hbad
                ·
                  exact fin15Anchored_clause22844 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22845 chi hbad
                ·
                  exact fin15Anchored_clause22846 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22847 chi hbad
                ·
                  exact fin15Anchored_clause22848 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22849 chi hbad
                ·
                  exact fin15Anchored_clause22850 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22851 chi hbad
                ·
                  exact fin15Anchored_clause22852 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22853 chi hbad
                ·
                  exact fin15Anchored_clause22854 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22855 chi hbad
                ·
                  exact fin15Anchored_clause22856 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22857 chi hbad
                ·
                  exact fin15Anchored_clause22858 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22859 chi hbad
                ·
                  exact fin15Anchored_clause22860 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22861 chi hbad
                ·
                  exact fin15Anchored_clause22862 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22863 chi hbad
                ·
                  exact fin15Anchored_clause22864 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22865 chi hbad
                ·
                  exact fin15Anchored_clause22866 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22867 chi hbad
                ·
                  exact fin15Anchored_clause22868 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22869 chi hbad
                ·
                  exact fin15Anchored_clause22870 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22871 chi hbad
                ·
                  exact fin15Anchored_clause22872 chi hbad
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
                  exact fin15Anchored_clause22873 chi hbad
                ·
                  exact fin15Anchored_clause22874 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22875 chi hbad
                ·
                  exact fin15Anchored_clause22876 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22877 chi hbad
                ·
                  exact fin15Anchored_clause22878 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22879 chi hbad
                ·
                  exact fin15Anchored_clause22880 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22881 chi hbad
                ·
                  exact fin15Anchored_clause22882 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22883 chi hbad
                ·
                  exact fin15Anchored_clause22884 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22885 chi hbad
                ·
                  exact fin15Anchored_clause22886 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22887 chi hbad
                ·
                  exact fin15Anchored_clause22888 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22889 chi hbad
                ·
                  exact fin15Anchored_clause22890 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22891 chi hbad
                ·
                  exact fin15Anchored_clause22892 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22893 chi hbad
                ·
                  exact fin15Anchored_clause22894 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22895 chi hbad
                ·
                  exact fin15Anchored_clause22896 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22897 chi hbad
                ·
                  exact fin15Anchored_clause22898 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22899 chi hbad
                ·
                  exact fin15Anchored_clause22900 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22901 chi hbad
                ·
                  exact fin15Anchored_clause22902 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22903 chi hbad
                ·
                  exact fin15Anchored_clause22904 chi hbad
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
                exact fin15Anchored_clause22905 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22906 chi hbad
                ·
                  exact fin15Anchored_clause22907 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22908 chi hbad
                ·
                  exact fin15Anchored_clause22909 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22910 chi hbad
                ·
                  exact fin15Anchored_clause22911 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22912 chi hbad
                ·
                  exact fin15Anchored_clause22913 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22914 chi hbad
                ·
                  exact fin15Anchored_clause22915 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22916 chi hbad
                ·
                  exact fin15Anchored_clause22917 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22918 chi hbad
                ·
                  exact fin15Anchored_clause22919 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22920 chi hbad
                ·
                  exact fin15Anchored_clause22921 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22922 chi hbad
                ·
                  exact fin15Anchored_clause22923 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22924 chi hbad
                ·
                  exact fin15Anchored_clause22925 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22926 chi hbad
                ·
                  exact fin15Anchored_clause22927 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22928 chi hbad
                ·
                  exact fin15Anchored_clause22929 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22930 chi hbad
                ·
                  exact fin15Anchored_clause22931 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22932 chi hbad
                ·
                  exact fin15Anchored_clause22933 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22934 chi hbad
                ·
                  exact fin15Anchored_clause22935 chi hbad
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
                  exact fin15Anchored_clause22936 chi hbad
                ·
                  exact fin15Anchored_clause22937 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22938 chi hbad
                ·
                  exact fin15Anchored_clause22939 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22940 chi hbad
                ·
                  exact fin15Anchored_clause22941 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22942 chi hbad
                ·
                  exact fin15Anchored_clause22943 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22944 chi hbad
                ·
                  exact fin15Anchored_clause22945 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22946 chi hbad
                ·
                  exact fin15Anchored_clause22947 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22948 chi hbad
                ·
                  exact fin15Anchored_clause22949 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22950 chi hbad
                ·
                  exact fin15Anchored_clause22951 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22952 chi hbad
                ·
                  exact fin15Anchored_clause22953 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22954 chi hbad
                ·
                  exact fin15Anchored_clause22955 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22956 chi hbad
                ·
                  exact fin15Anchored_clause22957 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22958 chi hbad
                ·
                  exact fin15Anchored_clause22959 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22960 chi hbad
                ·
                  exact fin15Anchored_clause22961 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22962 chi hbad
                ·
                  exact fin15Anchored_clause22963 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22964 chi hbad
                ·
                  exact fin15Anchored_clause22965 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22966 chi hbad
                ·
                  exact fin15Anchored_clause22967 chi hbad

end ErdosSzekeres

end
