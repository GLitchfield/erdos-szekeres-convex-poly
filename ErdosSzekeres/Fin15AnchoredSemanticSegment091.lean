module

public import ErdosSzekeres.Fin15AnchoredClauseChunk179
public import ErdosSzekeres.Fin15AnchoredClauseChunk180
public import ErdosSzekeres.Fin15AnchoredClauseChunk181

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 091. -/

theorem fin15Anchored_rejectSemanticSegment091
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom1032 chi) ∨
      ((Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom1033 chi) ∨
      (Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom1047 chi))) ∨
      (((Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom1083 chi) ∨
      (Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom1728 chi)) ∨
      ((¬Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1728 chi) ∨
      (Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom1032 chi)))) ∨
      ((((Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom1034 chi) ∨
      (Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom1048 chi)) ∨
      ((Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom1729 chi) ∨
      (¬Fin15AnchoredAtom3445 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1034 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1729 chi))) ∨
      (((Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom1033 chi) ∨
      (Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom1034 chi)) ∨
      ((Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom1049 chi) ∨
      (Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom1730 chi))))) ∨
      (((((¬Fin15AnchoredAtom3446 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1034 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1730 chi) ∨
      (Fin15AnchoredAtom3447 chi ∧
      ¬Fin15AnchoredAtom1035 chi)) ∨
      ((Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom1035 chi) ∨
      (Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom1037 chi))) ∨
      (((Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom1041 chi) ∨
      (Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom1087 chi)) ∨
      ((Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom1732 chi) ∨
      (¬Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1732 chi)))) ∨
      ((((Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom1035 chi) ∨
      (Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom1038 chi)) ∨
      ((Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom1042 chi) ∨
      (Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom1088 chi))) ∨
      (((Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom1733 chi) ∨
      (¬Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1733 chi)) ∨
      ((Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom1035 chi) ∨
      (Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom1039 chi)))))) ∨
      ((((((Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom1043 chi) ∨
      (Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom1089 chi)) ∨
      ((Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom1734 chi) ∨
      (¬Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1734 chi))) ∨
      (((Fin15AnchoredAtom3451 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (Fin15AnchoredAtom3451 chi ∧
      ¬Fin15AnchoredAtom1735 chi)) ∨
      ((¬Fin15AnchoredAtom3451 chi ∧
      Fin15AnchoredAtom1036 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1044 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1735 chi) ∨
      (Fin15AnchoredAtom3452 chi ∧
      ¬Fin15AnchoredAtom1038 chi)))) ∨
      ((((Fin15AnchoredAtom3452 chi ∧
      ¬Fin15AnchoredAtom1736 chi) ∨
      (Fin15AnchoredAtom3453 chi ∧
      ¬Fin15AnchoredAtom1039 chi)) ∨
      ((Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom1038 chi))) ∨
      (((Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom1047 chi) ∨
      (Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom1093 chi)) ∨
      ((Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom1738 chi) ∨
      (¬Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1738 chi))))) ∨
      (((((Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom1039 chi)) ∨
      ((Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom1048 chi) ∨
      (Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom1094 chi))) ∨
      (((Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom1739 chi) ∨
      (¬Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1739 chi)) ∨
      ((Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom1038 chi) ∨
      (Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom1039 chi)))) ∨
      ((((Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom1049 chi) ∨
      (Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom1095 chi)) ∨
      ((Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom1740 chi) ∨
      (¬Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1740 chi))) ∨
      (((Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom1040 chi) ∨
      (Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom1041 chi)) ∨
      ((Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom1044 chi) ∨
      (Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom1741 chi))))))) ∨
      ((((((Fin15AnchoredAtom3458 chi ∧
      ¬Fin15AnchoredAtom1040 chi) ∨
      ((Fin15AnchoredAtom3458 chi ∧
      ¬Fin15AnchoredAtom1042 chi) ∨
      (Fin15AnchoredAtom3459 chi ∧
      ¬Fin15AnchoredAtom1040 chi))) ∨
      (((Fin15AnchoredAtom3459 chi ∧
      ¬Fin15AnchoredAtom1043 chi) ∨
      (Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom1041 chi)) ∨
      ((Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom1042 chi) ∨
      (Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom1047 chi)))) ∨
      ((((Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom1099 chi) ∨
      (Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom1744 chi)) ∨
      ((¬Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1744 chi) ∨
      (Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom1041 chi))) ∨
      (((Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom1043 chi) ∨
      (Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom1048 chi)) ∨
      ((Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom1100 chi) ∨
      (Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom1745 chi))))) ∨
      (((((¬Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1745 chi) ∨
      (Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom1042 chi)) ∨
      ((Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom1043 chi) ∨
      (Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom1049 chi))) ∨
      (((Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom1101 chi) ∨
      (Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom1746 chi)) ∨
      ((¬Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1746 chi) ∨
      (Fin15AnchoredAtom3463 chi ∧
      ¬Fin15AnchoredAtom1044 chi)))) ∨
      ((((Fin15AnchoredAtom3463 chi ∧
      ¬Fin15AnchoredAtom1047 chi) ∨
      (Fin15AnchoredAtom3463 chi ∧
      ¬Fin15AnchoredAtom1747 chi)) ∨
      ((Fin15AnchoredAtom3464 chi ∧
      ¬Fin15AnchoredAtom1044 chi) ∨
      (Fin15AnchoredAtom3464 chi ∧
      ¬Fin15AnchoredAtom1048 chi))) ∨
      (((Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom1047 chi) ∨
      (Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom1048 chi)) ∨
      ((Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom1049 chi) ∨
      (Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom1105 chi)))))) ∨
      ((((((Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom1750 chi) ∨
      (¬Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1750 chi)) ∨
      ((Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom1050 chi) ∨
      (Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom1051 chi))) ∨
      (((Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom1751 chi)) ∨
      ((¬Fin15AnchoredAtom3467 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1751 chi) ∨
      (Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom1050 chi)))) ∨
      ((((Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom1053 chi) ∨
      (Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom1058 chi)) ∨
      ((Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom1073 chi) ∨
      (Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom1753 chi))) ∨
      (((¬Fin15AnchoredAtom3469 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1753 chi) ∨
      (Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom1050 chi)) ∨
      ((Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom1054 chi) ∨
      (Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom1059 chi))))) ∨
      (((((Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom1754 chi) ∨
      (¬Fin15AnchoredAtom3470 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1754 chi)) ∨
      ((Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom1050 chi) ∨
      (Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom1060 chi))) ∨
      (((Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom1075 chi) ∨
      (Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom1755 chi)) ∨
      ((¬Fin15AnchoredAtom3471 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1075 chi ∧
      Fin15AnchoredAtom1755 chi) ∨
      (Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom1051 chi)))) ∨
      ((((Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom1053 chi) ∨
      (Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom1062 chi)) ∨
      ((Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom1757 chi) ∨
      (¬Fin15AnchoredAtom3473 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1757 chi))) ∨
      (((Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom1051 chi) ∨
      (Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom1054 chi)) ∨
      ((Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom1063 chi) ∨
      (Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom1078 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom1758 chi) ∨
      ((Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom1051 chi) ∨
      (Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom1055 chi))) ∨
      (((Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom1064 chi) ∨
      (Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom1759 chi)) ∨
      ((Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom1053 chi) ∨
      (Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom1054 chi)))) ∨
      ((((Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom1068 chi) ∨
      (Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom1083 chi)) ∨
      ((Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom1763 chi) ∨
      (¬Fin15AnchoredAtom3479 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1763 chi))) ∨
      (((Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom1053 chi) ∨
      (Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom1055 chi)) ∨
      ((Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom1069 chi) ∨
      (Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom1084 chi))))) ∨
      (((((Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom1764 chi) ∨
      (¬Fin15AnchoredAtom3480 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1764 chi)) ∨
      ((Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom1054 chi) ∨
      (Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom1055 chi))) ∨
      (((Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom1070 chi) ∨
      (Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom1085 chi)) ∨
      ((Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom1765 chi) ∨
      (¬Fin15AnchoredAtom3481 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1765 chi)))) ∨
      ((((Fin15AnchoredAtom3482 chi ∧
      ¬Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom3482 chi ∧
      ¬Fin15AnchoredAtom1766 chi)) ∨
      ((Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom1058 chi))) ∨
      (((Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom1062 chi) ∨
      (Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom1087 chi)) ∨
      ((Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom1767 chi) ∨
      (¬Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1767 chi)))))) ∨
      ((((((Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom1059 chi)) ∨
      ((Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom1063 chi) ∨
      (Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom1088 chi))) ∨
      (((Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom1768 chi) ∨
      (¬Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1768 chi)) ∨
      ((Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom1060 chi)))) ∨
      ((((Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom1064 chi) ∨
      (Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom1089 chi)) ∨
      ((Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom1769 chi) ∨
      (¬Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1769 chi))) ∨
      (((Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom1058 chi) ∨
      (Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom1065 chi)) ∨
      ((Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom1770 chi) ∨
      (¬Fin15AnchoredAtom3486 chi ∧
      Fin15AnchoredAtom1057 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1065 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1770 chi))))) ∨
      (((((Fin15AnchoredAtom3487 chi ∧
      ¬Fin15AnchoredAtom1059 chi) ∨
      (Fin15AnchoredAtom3488 chi ∧
      ¬Fin15AnchoredAtom1060 chi)) ∨
      ((Fin15AnchoredAtom3488 chi ∧
      ¬Fin15AnchoredAtom1067 chi) ∨
      (Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom1058 chi))) ∨
      (((Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom1059 chi) ∨
      (Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom1068 chi)) ∨
      ((Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom1093 chi) ∨
      (Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom1773 chi)))) ∨
      ((((¬Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1773 chi) ∨
      (Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom1058 chi)) ∨
      ((Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom1060 chi) ∨
      (Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom1069 chi))) ∨
      (((Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom1094 chi) ∨
      (Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom1774 chi)) ∨
      ((¬Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1774 chi) ∨
      (Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom1059 chi))))))) ∨
      (((((((Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom1060 chi) ∨
      (Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom1070 chi)) ∨
      ((Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom1095 chi) ∨
      (Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom1775 chi))) ∨
      (((¬Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1775 chi) ∨
      (Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom1062 chi)) ∨
      ((Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom1096 chi) ∨
      (Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom1776 chi)))) ∨
      ((((Fin15AnchoredAtom3493 chi ∧
      ¬Fin15AnchoredAtom1063 chi) ∨
      (Fin15AnchoredAtom3494 chi ∧
      ¬Fin15AnchoredAtom1064 chi)) ∨
      ((Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom1062 chi) ∨
      (Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom1063 chi))) ∨
      (((Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom1068 chi) ∨
      (Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom1099 chi)) ∨
      ((Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom1779 chi) ∨
      (¬Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1779 chi))))) ∨
      (((((Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom1062 chi) ∨
      (Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom1064 chi)) ∨
      ((Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom1069 chi) ∨
      (Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom1100 chi))) ∨
      (((Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom1780 chi) ∨
      (¬Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1780 chi)) ∨
      ((Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom1063 chi) ∨
      (Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom1064 chi)))) ∨
      ((((Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom1070 chi) ∨
      (Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom1101 chi)) ∨
      ((Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom1781 chi) ∨
      (¬Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1781 chi))) ∨
      (((Fin15AnchoredAtom3498 chi ∧
      ¬Fin15AnchoredAtom1068 chi) ∨
      (Fin15AnchoredAtom3498 chi ∧
      ¬Fin15AnchoredAtom1782 chi)) ∨
      ((Fin15AnchoredAtom3499 chi ∧
      ¬Fin15AnchoredAtom1069 chi) ∨
      (Fin15AnchoredAtom3500 chi ∧
      ¬Fin15AnchoredAtom1070 chi)))))) ∨
      ((((((Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom1068 chi) ∨
      (Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom1069 chi)) ∨
      ((Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom1070 chi) ∨
      (Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom1105 chi))) ∨
      (((Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom1785 chi) ∨
      (¬Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1785 chi)) ∨
      ((Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom1071 chi) ∨
      (Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom1073 chi)))) ∨
      ((((Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom1077 chi) ∨
      (Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom1087 chi)) ∨
      ((Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom1787 chi) ∨
      (¬Fin15AnchoredAtom3503 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1787 chi))) ∨
      (((Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom1071 chi) ∨
      (Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom1074 chi)) ∨
      ((Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom1078 chi) ∨
      (Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom1088 chi))))) ∨
      (((((Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom1788 chi) ∨
      (¬Fin15AnchoredAtom3504 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1788 chi)) ∨
      ((Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom1071 chi) ∨
      (Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom1075 chi))) ∨
      (((Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom1079 chi) ∨
      (Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom1089 chi)) ∨
      ((Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom1789 chi) ∨
      (Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom1073 chi)))) ∨
      ((((Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom1074 chi) ∨
      (Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom1083 chi)) ∨
      ((Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom1093 chi) ∨
      (Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom1793 chi))) ∨
      (((¬Fin15AnchoredAtom3509 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1793 chi) ∨
      (Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom1073 chi)) ∨
      ((Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom1075 chi) ∨
      (Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom1094 chi)))))))))) := by
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
                exact fin15Anchored_clause22968 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22969 chi hbad
                ·
                  exact fin15Anchored_clause22970 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22971 chi hbad
                ·
                  exact fin15Anchored_clause22972 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22973 chi hbad
                ·
                  exact fin15Anchored_clause22974 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22975 chi hbad
                ·
                  exact fin15Anchored_clause22976 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22977 chi hbad
                ·
                  exact fin15Anchored_clause22978 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22979 chi hbad
                ·
                  exact fin15Anchored_clause22980 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22981 chi hbad
                ·
                  exact fin15Anchored_clause22982 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22983 chi hbad
                ·
                  exact fin15Anchored_clause22984 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22985 chi hbad
                ·
                  exact fin15Anchored_clause22986 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22987 chi hbad
                ·
                  exact fin15Anchored_clause22988 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22989 chi hbad
                ·
                  exact fin15Anchored_clause22990 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22991 chi hbad
                ·
                  exact fin15Anchored_clause22992 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22993 chi hbad
                ·
                  exact fin15Anchored_clause22994 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22995 chi hbad
                ·
                  exact fin15Anchored_clause22996 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22997 chi hbad
                ·
                  exact fin15Anchored_clause22998 chi hbad
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
                  exact fin15Anchored_clause22999 chi hbad
                ·
                  exact fin15Anchored_clause23000 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23001 chi hbad
                ·
                  exact fin15Anchored_clause23002 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23003 chi hbad
                ·
                  exact fin15Anchored_clause23004 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23005 chi hbad
                ·
                  exact fin15Anchored_clause23006 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23007 chi hbad
                ·
                  exact fin15Anchored_clause23008 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23009 chi hbad
                ·
                  exact fin15Anchored_clause23010 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23011 chi hbad
                ·
                  exact fin15Anchored_clause23012 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23013 chi hbad
                ·
                  exact fin15Anchored_clause23014 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23015 chi hbad
                ·
                  exact fin15Anchored_clause23016 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23017 chi hbad
                ·
                  exact fin15Anchored_clause23018 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23019 chi hbad
                ·
                  exact fin15Anchored_clause23020 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23021 chi hbad
                ·
                  exact fin15Anchored_clause23022 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23023 chi hbad
                ·
                  exact fin15Anchored_clause23024 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23025 chi hbad
                ·
                  exact fin15Anchored_clause23026 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23027 chi hbad
                ·
                  exact fin15Anchored_clause23028 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23029 chi hbad
                ·
                  exact fin15Anchored_clause23030 chi hbad
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
                exact fin15Anchored_clause23031 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23032 chi hbad
                ·
                  exact fin15Anchored_clause23033 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23034 chi hbad
                ·
                  exact fin15Anchored_clause23035 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23036 chi hbad
                ·
                  exact fin15Anchored_clause23037 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23038 chi hbad
                ·
                  exact fin15Anchored_clause23039 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23040 chi hbad
                ·
                  exact fin15Anchored_clause23041 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23042 chi hbad
                ·
                  exact fin15Anchored_clause23043 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23044 chi hbad
                ·
                  exact fin15Anchored_clause23045 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23046 chi hbad
                ·
                  exact fin15Anchored_clause23047 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23048 chi hbad
                ·
                  exact fin15Anchored_clause23049 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23050 chi hbad
                ·
                  exact fin15Anchored_clause23051 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23052 chi hbad
                ·
                  exact fin15Anchored_clause23053 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23054 chi hbad
                ·
                  exact fin15Anchored_clause23055 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23056 chi hbad
                ·
                  exact fin15Anchored_clause23057 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23058 chi hbad
                ·
                  exact fin15Anchored_clause23059 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23060 chi hbad
                ·
                  exact fin15Anchored_clause23061 chi hbad
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
                  exact fin15Anchored_clause23062 chi hbad
                ·
                  exact fin15Anchored_clause23063 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23064 chi hbad
                ·
                  exact fin15Anchored_clause23065 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23066 chi hbad
                ·
                  exact fin15Anchored_clause23067 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23068 chi hbad
                ·
                  exact fin15Anchored_clause23069 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23070 chi hbad
                ·
                  exact fin15Anchored_clause23071 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23072 chi hbad
                ·
                  exact fin15Anchored_clause23073 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23074 chi hbad
                ·
                  exact fin15Anchored_clause23075 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23076 chi hbad
                ·
                  exact fin15Anchored_clause23077 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23078 chi hbad
                ·
                  exact fin15Anchored_clause23079 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23080 chi hbad
                ·
                  exact fin15Anchored_clause23081 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23082 chi hbad
                ·
                  exact fin15Anchored_clause23083 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23084 chi hbad
                ·
                  exact fin15Anchored_clause23085 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23086 chi hbad
                ·
                  exact fin15Anchored_clause23087 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23088 chi hbad
                ·
                  exact fin15Anchored_clause23089 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23090 chi hbad
                ·
                  exact fin15Anchored_clause23091 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23092 chi hbad
                ·
                  exact fin15Anchored_clause23093 chi hbad
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
                exact fin15Anchored_clause23094 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23095 chi hbad
                ·
                  exact fin15Anchored_clause23096 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23097 chi hbad
                ·
                  exact fin15Anchored_clause23098 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23099 chi hbad
                ·
                  exact fin15Anchored_clause23100 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23101 chi hbad
                ·
                  exact fin15Anchored_clause23102 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23103 chi hbad
                ·
                  exact fin15Anchored_clause23104 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23105 chi hbad
                ·
                  exact fin15Anchored_clause23106 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23107 chi hbad
                ·
                  exact fin15Anchored_clause23108 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23109 chi hbad
                ·
                  exact fin15Anchored_clause23110 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23111 chi hbad
                ·
                  exact fin15Anchored_clause23112 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23113 chi hbad
                ·
                  exact fin15Anchored_clause23114 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23115 chi hbad
                ·
                  exact fin15Anchored_clause23116 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23117 chi hbad
                ·
                  exact fin15Anchored_clause23118 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23119 chi hbad
                ·
                  exact fin15Anchored_clause23120 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23121 chi hbad
                ·
                  exact fin15Anchored_clause23122 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23123 chi hbad
                ·
                  exact fin15Anchored_clause23124 chi hbad
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
                  exact fin15Anchored_clause23125 chi hbad
                ·
                  exact fin15Anchored_clause23126 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23127 chi hbad
                ·
                  exact fin15Anchored_clause23128 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23129 chi hbad
                ·
                  exact fin15Anchored_clause23130 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23131 chi hbad
                ·
                  exact fin15Anchored_clause23132 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23133 chi hbad
                ·
                  exact fin15Anchored_clause23134 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23135 chi hbad
                ·
                  exact fin15Anchored_clause23136 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23137 chi hbad
                ·
                  exact fin15Anchored_clause23138 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23139 chi hbad
                ·
                  exact fin15Anchored_clause23140 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23141 chi hbad
                ·
                  exact fin15Anchored_clause23142 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23143 chi hbad
                ·
                  exact fin15Anchored_clause23144 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23145 chi hbad
                ·
                  exact fin15Anchored_clause23146 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23147 chi hbad
                ·
                  exact fin15Anchored_clause23148 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23149 chi hbad
                ·
                  exact fin15Anchored_clause23150 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23151 chi hbad
                ·
                  exact fin15Anchored_clause23152 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23153 chi hbad
                ·
                  exact fin15Anchored_clause23154 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23155 chi hbad
                ·
                  exact fin15Anchored_clause23156 chi hbad
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
                  exact fin15Anchored_clause23157 chi hbad
                ·
                  exact fin15Anchored_clause23158 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23159 chi hbad
                ·
                  exact fin15Anchored_clause23160 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23161 chi hbad
                ·
                  exact fin15Anchored_clause23162 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23163 chi hbad
                ·
                  exact fin15Anchored_clause23164 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23165 chi hbad
                ·
                  exact fin15Anchored_clause23166 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23167 chi hbad
                ·
                  exact fin15Anchored_clause23168 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23169 chi hbad
                ·
                  exact fin15Anchored_clause23170 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23171 chi hbad
                ·
                  exact fin15Anchored_clause23172 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23173 chi hbad
                ·
                  exact fin15Anchored_clause23174 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23175 chi hbad
                ·
                  exact fin15Anchored_clause23176 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23177 chi hbad
                ·
                  exact fin15Anchored_clause23178 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23179 chi hbad
                ·
                  exact fin15Anchored_clause23180 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23181 chi hbad
                ·
                  exact fin15Anchored_clause23182 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23183 chi hbad
                ·
                  exact fin15Anchored_clause23184 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23185 chi hbad
                ·
                  exact fin15Anchored_clause23186 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23187 chi hbad
                ·
                  exact fin15Anchored_clause23188 chi hbad
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
                  exact fin15Anchored_clause23189 chi hbad
                ·
                  exact fin15Anchored_clause23190 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23191 chi hbad
                ·
                  exact fin15Anchored_clause23192 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23193 chi hbad
                ·
                  exact fin15Anchored_clause23194 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23195 chi hbad
                ·
                  exact fin15Anchored_clause23196 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23197 chi hbad
                ·
                  exact fin15Anchored_clause23198 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23199 chi hbad
                ·
                  exact fin15Anchored_clause23200 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23201 chi hbad
                ·
                  exact fin15Anchored_clause23202 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23203 chi hbad
                ·
                  exact fin15Anchored_clause23204 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23205 chi hbad
                ·
                  exact fin15Anchored_clause23206 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23207 chi hbad
                ·
                  exact fin15Anchored_clause23208 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23209 chi hbad
                ·
                  exact fin15Anchored_clause23210 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23211 chi hbad
                ·
                  exact fin15Anchored_clause23212 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23213 chi hbad
                ·
                  exact fin15Anchored_clause23214 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23215 chi hbad
                ·
                  exact fin15Anchored_clause23216 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23217 chi hbad
                ·
                  exact fin15Anchored_clause23218 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause23219 chi hbad
                ·
                  exact fin15Anchored_clause23220 chi hbad

end ErdosSzekeres

end
