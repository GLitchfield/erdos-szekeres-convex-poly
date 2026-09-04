module

public import ErdosSzekeres.Fin15AnchoredClauseChunk167
public import ErdosSzekeres.Fin15AnchoredClauseChunk168
public import ErdosSzekeres.Fin15AnchoredClauseChunk169

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 085. -/

theorem fin15Anchored_rejectSemanticSegment085
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom0902 chi) ∨
      ((Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom0917 chi) ∨
      (Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom0998 chi))) ∨
      (((Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom1383 chi) ∨
      (¬Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1383 chi)) ∨
      ((Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom0897 chi) ∨
      (Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom0903 chi)))) ∨
      ((((Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom0918 chi) ∨
      (Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom0999 chi)) ∨
      ((Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom1384 chi) ∨
      (¬Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1384 chi))) ∨
      (((Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom0897 chi) ∨
      (Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom0904 chi)) ∨
      ((Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom0919 chi) ∨
      (Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom1000 chi))))) ∨
      (((((Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom1385 chi) ∨
      (¬Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1385 chi)) ∨
      ((Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom0898 chi) ∨
      (Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom0899 chi))) ∨
      (((Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom1001 chi) ∨
      (Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom1386 chi)) ∨
      ((¬Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1386 chi) ∨
      (Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom0898 chi)))) ∨
      ((((Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom0900 chi) ∨
      (Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom0921 chi)) ∨
      ((Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom1002 chi) ∨
      (Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom1387 chi))) ∨
      (((¬Fin15AnchoredAtom3103 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1387 chi) ∨
      (Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom0898 chi)) ∨
      ((Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom0902 chi) ∨
      (Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom1389 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3105 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1389 chi) ∨
      (Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom0898 chi)) ∨
      ((Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom0903 chi) ∨
      (Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom0924 chi))) ∨
      (((Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom1005 chi) ∨
      (Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom1390 chi)) ∨
      ((¬Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1390 chi) ∨
      (Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom0898 chi)))) ∨
      ((((Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom0904 chi) ∨
      (Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom1006 chi)) ∨
      ((Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom1391 chi) ∨
      (¬Fin15AnchoredAtom3107 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom1006 chi ∧
      Fin15AnchoredAtom1391 chi))) ∨
      (((Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom0899 chi) ∨
      (Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom0900 chi)) ∨
      ((Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom0926 chi) ∨
      (Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom1007 chi))))) ∨
      (((((Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom1392 chi) ∨
      (¬Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1392 chi)) ∨
      ((Fin15AnchoredAtom3109 chi ∧
      ¬Fin15AnchoredAtom0927 chi) ∨
      (Fin15AnchoredAtom3109 chi ∧
      ¬Fin15AnchoredAtom1008 chi))) ∨
      (((Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom0899 chi) ∨
      (Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom0902 chi)) ∨
      ((Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom0928 chi) ∨
      (Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom1009 chi)))) ∨
      ((((Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom1394 chi) ∨
      (¬Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1394 chi)) ∨
      ((Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom0899 chi) ∨
      (Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom0903 chi))) ∨
      (((Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom0929 chi) ∨
      (Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom1010 chi)) ∨
      ((Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom1395 chi) ∨
      (¬Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1395 chi))))))) ∨
      ((((((Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom0899 chi) ∨
      ((Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom0904 chi) ∨
      (Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom0930 chi))) ∨
      (((Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom1011 chi) ∨
      (Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom1396 chi)) ∨
      ((¬Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1396 chi) ∨
      (Fin15AnchoredAtom3113 chi ∧
      ¬Fin15AnchoredAtom0900 chi)))) ∨
      ((((Fin15AnchoredAtom3113 chi ∧
      ¬Fin15AnchoredAtom0901 chi) ∨
      (Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom0900 chi)) ∨
      ((Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom0902 chi) ∨
      (Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom0932 chi))) ∨
      (((Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom1013 chi) ∨
      (Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom1398 chi)) ∨
      ((¬Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1398 chi) ∨
      (Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom0900 chi))))) ∨
      (((((Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom0903 chi) ∨
      (Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom0933 chi)) ∨
      ((Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom1014 chi) ∨
      (Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom1399 chi))) ∨
      (((¬Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1399 chi) ∨
      (Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom0900 chi)) ∨
      ((Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom0904 chi) ∨
      (Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom0934 chi)))) ∨
      ((((Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom1015 chi) ∨
      (Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom1400 chi)) ∨
      ((¬Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1400 chi) ∨
      (Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom0901 chi))) ∨
      (((Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom0935 chi) ∨
      (Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom1016 chi)) ∨
      ((Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom1401 chi) ∨
      (Fin15AnchoredAtom3119 chi ∧
      ¬Fin15AnchoredAtom0904 chi)))))) ∨
      ((((((Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom0902 chi) ∨
      (Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom0903 chi)) ∨
      ((Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom0938 chi) ∨
      (Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom1019 chi))) ∨
      (((Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom1404 chi) ∨
      (¬Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1404 chi)) ∨
      ((Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom0902 chi) ∨
      (Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom0904 chi)))) ∨
      ((((Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom0939 chi) ∨
      (Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom1020 chi)) ∨
      ((Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom1405 chi) ∨
      (¬Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1405 chi))) ∨
      (((Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom0903 chi) ∨
      (Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom0904 chi)) ∨
      ((Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom0940 chi) ∨
      (Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom1021 chi))))) ∨
      (((((Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom1406 chi) ∨
      (¬Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1406 chi)) ∨
      ((Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom0905 chi) ∨
      (Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom1022 chi))) ∨
      (((Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom1407 chi) ∨
      (¬Fin15AnchoredAtom3123 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1407 chi)) ∨
      ((Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom0905 chi) ∨
      (Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom0907 chi)))) ∨
      ((((Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom0914 chi) ∨
      (Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom1023 chi)) ∨
      ((Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom1408 chi) ∨
      (¬Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1408 chi))) ∨
      (((Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom0905 chi) ∨
      (Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom0908 chi)) ∨
      ((Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom0915 chi) ∨
      (Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom1024 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom1409 chi) ∨
      ((¬Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1409 chi) ∨
      (Fin15AnchoredAtom3126 chi ∧
      ¬Fin15AnchoredAtom0905 chi))) ∨
      (((Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom0905 chi) ∨
      (Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom0910 chi)) ∨
      ((Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom0917 chi) ∨
      (Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom1026 chi)))) ∨
      ((((Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom1411 chi) ∨
      (¬Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1411 chi)) ∨
      ((Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom0905 chi) ∨
      (Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom0911 chi))) ∨
      (((Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom0918 chi) ∨
      (Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom1027 chi)) ∨
      ((Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom1412 chi) ∨
      (¬Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1412 chi))))) ∨
      (((((Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom0905 chi) ∨
      (Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom0912 chi)) ∨
      ((Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom0919 chi) ∨
      (Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom1028 chi))) ∨
      (((Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom1413 chi) ∨
      (¬Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1413 chi)) ∨
      ((Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom0906 chi) ∨
      (Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom0907 chi)))) ∨
      ((((Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom0920 chi) ∨
      (Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom1414 chi)) ∨
      ((¬Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1414 chi) ∨
      (Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom0908 chi))) ∨
      (((Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom0921 chi) ∨
      (Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom1030 chi)) ∨
      ((Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom1415 chi) ∨
      (¬Fin15AnchoredAtom3131 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1415 chi)))))) ∨
      ((((((Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom0906 chi) ∨
      (Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom0910 chi)) ∨
      ((Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom0923 chi) ∨
      (Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom1032 chi))) ∨
      (((Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom1417 chi) ∨
      (¬Fin15AnchoredAtom3133 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1417 chi)) ∨
      ((Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom0906 chi) ∨
      (Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom0911 chi)))) ∨
      ((((Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom0924 chi) ∨
      (Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom1033 chi)) ∨
      ((Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom1418 chi) ∨
      (¬Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1418 chi))) ∨
      (((Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom0906 chi) ∨
      (Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom0912 chi)) ∨
      ((Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom1034 chi) ∨
      (Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom1419 chi))))) ∨
      (((((¬Fin15AnchoredAtom3135 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom1034 chi ∧
      Fin15AnchoredAtom1419 chi) ∨
      (Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom0907 chi)) ∨
      ((Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom0908 chi) ∨
      (Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom0926 chi))) ∨
      (((Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom1035 chi) ∨
      (Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom1420 chi)) ∨
      ((¬Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1420 chi) ∨
      (Fin15AnchoredAtom3137 chi ∧
      ¬Fin15AnchoredAtom0907 chi)))) ∨
      ((((Fin15AnchoredAtom3137 chi ∧
      ¬Fin15AnchoredAtom1421 chi) ∨
      (Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom0907 chi)) ∨
      ((Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom0910 chi) ∨
      (Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom0928 chi))) ∨
      (((Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom1422 chi)) ∨
      ((¬Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1422 chi) ∨
      (Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom0907 chi))))))) ∨
      (((((((Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom0911 chi) ∨
      (Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom0929 chi)) ∨
      ((Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom1038 chi) ∨
      (Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom1423 chi))) ∨
      (((¬Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1423 chi) ∨
      (Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom0907 chi)) ∨
      ((Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom0912 chi) ∨
      (Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom0930 chi)))) ∨
      ((((Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom1039 chi) ∨
      (Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom1424 chi)) ∨
      ((¬Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1424 chi) ∨
      (Fin15AnchoredAtom3141 chi ∧
      ¬Fin15AnchoredAtom0908 chi))) ∨
      (((Fin15AnchoredAtom3141 chi ∧
      ¬Fin15AnchoredAtom0909 chi) ∨
      (Fin15AnchoredAtom3141 chi ∧
      ¬Fin15AnchoredAtom1425 chi)) ∨
      ((Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom0908 chi) ∨
      (Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom0910 chi))))) ∨
      (((((Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom0932 chi) ∨
      (Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom1041 chi)) ∨
      ((Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom1426 chi) ∨
      (¬Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1426 chi))) ∨
      (((Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom0908 chi) ∨
      (Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom0911 chi)) ∨
      ((Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom0933 chi) ∨
      (Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom1042 chi)))) ∨
      ((((Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom1427 chi) ∨
      (¬Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1427 chi)) ∨
      ((Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom0908 chi) ∨
      (Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom0912 chi))) ∨
      (((Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom0934 chi) ∨
      (Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom1043 chi)) ∨
      ((Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom1428 chi) ∨
      (¬Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1428 chi)))))) ∨
      ((((((Fin15AnchoredAtom3145 chi ∧
      ¬Fin15AnchoredAtom1044 chi) ∨
      (Fin15AnchoredAtom3145 chi ∧
      ¬Fin15AnchoredAtom1429 chi)) ∨
      ((¬Fin15AnchoredAtom3145 chi ∧
      Fin15AnchoredAtom0909 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0935 chi ∧
      Fin15AnchoredAtom1044 chi ∧
      Fin15AnchoredAtom1429 chi) ∨
      (Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom0910 chi))) ∨
      (((Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom0911 chi) ∨
      (Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom0938 chi)) ∨
      ((Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom1047 chi) ∨
      (Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom1432 chi)))) ∨
      ((((¬Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1432 chi) ∨
      (Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom0910 chi)) ∨
      ((Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom0912 chi) ∨
      (Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom0939 chi))) ∨
      (((Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom1048 chi) ∨
      (Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom1433 chi)) ∨
      ((¬Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1433 chi) ∨
      (Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom0911 chi))))) ∨
      (((((Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom0912 chi) ∨
      (Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom0940 chi)) ∨
      ((Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom1049 chi) ∨
      (Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom1434 chi))) ∨
      (((¬Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1434 chi) ∨
      (Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom0913 chi)) ∨
      ((Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom0914 chi) ∨
      (Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom0920 chi)))) ∨
      ((((Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom1050 chi) ∨
      (Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom1435 chi)) ∨
      ((¬Fin15AnchoredAtom3151 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1435 chi) ∨
      (Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom0913 chi))) ∨
      (((Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom0915 chi) ∨
      (Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom1051 chi)) ∨
      ((Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom1436 chi) ∨
      (¬Fin15AnchoredAtom3152 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1436 chi)))))))))) := by
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
                exact fin15Anchored_clause21453 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21454 chi hbad
                ·
                  exact fin15Anchored_clause21455 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21456 chi hbad
                ·
                  exact fin15Anchored_clause21457 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21458 chi hbad
                ·
                  exact fin15Anchored_clause21459 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21460 chi hbad
                ·
                  exact fin15Anchored_clause21461 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21462 chi hbad
                ·
                  exact fin15Anchored_clause21463 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21464 chi hbad
                ·
                  exact fin15Anchored_clause21465 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21466 chi hbad
                ·
                  exact fin15Anchored_clause21467 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21468 chi hbad
                ·
                  exact fin15Anchored_clause21469 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21470 chi hbad
                ·
                  exact fin15Anchored_clause21471 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21472 chi hbad
                ·
                  exact fin15Anchored_clause21473 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21474 chi hbad
                ·
                  exact fin15Anchored_clause21475 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21476 chi hbad
                ·
                  exact fin15Anchored_clause21477 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21478 chi hbad
                ·
                  exact fin15Anchored_clause21479 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21480 chi hbad
                ·
                  exact fin15Anchored_clause21481 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21482 chi hbad
                ·
                  exact fin15Anchored_clause21483 chi hbad
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
                  exact fin15Anchored_clause21484 chi hbad
                ·
                  exact fin15Anchored_clause21485 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21486 chi hbad
                ·
                  exact fin15Anchored_clause21487 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21488 chi hbad
                ·
                  exact fin15Anchored_clause21489 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21490 chi hbad
                ·
                  exact fin15Anchored_clause21491 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21492 chi hbad
                ·
                  exact fin15Anchored_clause21493 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21494 chi hbad
                ·
                  exact fin15Anchored_clause21495 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21496 chi hbad
                ·
                  exact fin15Anchored_clause21497 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21498 chi hbad
                ·
                  exact fin15Anchored_clause21499 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21500 chi hbad
                ·
                  exact fin15Anchored_clause21501 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21502 chi hbad
                ·
                  exact fin15Anchored_clause21503 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21504 chi hbad
                ·
                  exact fin15Anchored_clause21505 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21506 chi hbad
                ·
                  exact fin15Anchored_clause21507 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21508 chi hbad
                ·
                  exact fin15Anchored_clause21509 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21510 chi hbad
                ·
                  exact fin15Anchored_clause21511 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21512 chi hbad
                ·
                  exact fin15Anchored_clause21513 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21514 chi hbad
                ·
                  exact fin15Anchored_clause21515 chi hbad
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
                exact fin15Anchored_clause21516 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21517 chi hbad
                ·
                  exact fin15Anchored_clause21518 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21519 chi hbad
                ·
                  exact fin15Anchored_clause21520 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21521 chi hbad
                ·
                  exact fin15Anchored_clause21522 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21523 chi hbad
                ·
                  exact fin15Anchored_clause21524 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21525 chi hbad
                ·
                  exact fin15Anchored_clause21526 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21527 chi hbad
                ·
                  exact fin15Anchored_clause21528 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21529 chi hbad
                ·
                  exact fin15Anchored_clause21530 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21531 chi hbad
                ·
                  exact fin15Anchored_clause21532 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21533 chi hbad
                ·
                  exact fin15Anchored_clause21534 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21535 chi hbad
                ·
                  exact fin15Anchored_clause21536 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21537 chi hbad
                ·
                  exact fin15Anchored_clause21538 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21539 chi hbad
                ·
                  exact fin15Anchored_clause21540 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21541 chi hbad
                ·
                  exact fin15Anchored_clause21542 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21543 chi hbad
                ·
                  exact fin15Anchored_clause21544 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21545 chi hbad
                ·
                  exact fin15Anchored_clause21546 chi hbad
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
                  exact fin15Anchored_clause21547 chi hbad
                ·
                  exact fin15Anchored_clause21548 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21549 chi hbad
                ·
                  exact fin15Anchored_clause21550 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21551 chi hbad
                ·
                  exact fin15Anchored_clause21552 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21553 chi hbad
                ·
                  exact fin15Anchored_clause21554 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21555 chi hbad
                ·
                  exact fin15Anchored_clause21556 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21557 chi hbad
                ·
                  exact fin15Anchored_clause21558 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21559 chi hbad
                ·
                  exact fin15Anchored_clause21560 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21561 chi hbad
                ·
                  exact fin15Anchored_clause21562 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21563 chi hbad
                ·
                  exact fin15Anchored_clause21564 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21565 chi hbad
                ·
                  exact fin15Anchored_clause21566 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21567 chi hbad
                ·
                  exact fin15Anchored_clause21568 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21569 chi hbad
                ·
                  exact fin15Anchored_clause21570 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21571 chi hbad
                ·
                  exact fin15Anchored_clause21572 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21573 chi hbad
                ·
                  exact fin15Anchored_clause21574 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21575 chi hbad
                ·
                  exact fin15Anchored_clause21576 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21577 chi hbad
                ·
                  exact fin15Anchored_clause21578 chi hbad
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
                exact fin15Anchored_clause21579 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21580 chi hbad
                ·
                  exact fin15Anchored_clause21581 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21582 chi hbad
                ·
                  exact fin15Anchored_clause21583 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21584 chi hbad
                ·
                  exact fin15Anchored_clause21585 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21586 chi hbad
                ·
                  exact fin15Anchored_clause21587 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21588 chi hbad
                ·
                  exact fin15Anchored_clause21589 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21590 chi hbad
                ·
                  exact fin15Anchored_clause21591 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21592 chi hbad
                ·
                  exact fin15Anchored_clause21593 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21594 chi hbad
                ·
                  exact fin15Anchored_clause21595 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21596 chi hbad
                ·
                  exact fin15Anchored_clause21597 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21598 chi hbad
                ·
                  exact fin15Anchored_clause21599 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21600 chi hbad
                ·
                  exact fin15Anchored_clause21601 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21602 chi hbad
                ·
                  exact fin15Anchored_clause21603 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21604 chi hbad
                ·
                  exact fin15Anchored_clause21605 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21606 chi hbad
                ·
                  exact fin15Anchored_clause21607 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21608 chi hbad
                ·
                  exact fin15Anchored_clause21609 chi hbad
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
                  exact fin15Anchored_clause21610 chi hbad
                ·
                  exact fin15Anchored_clause21611 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21612 chi hbad
                ·
                  exact fin15Anchored_clause21613 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21614 chi hbad
                ·
                  exact fin15Anchored_clause21615 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21616 chi hbad
                ·
                  exact fin15Anchored_clause21617 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21618 chi hbad
                ·
                  exact fin15Anchored_clause21619 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21620 chi hbad
                ·
                  exact fin15Anchored_clause21621 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21622 chi hbad
                ·
                  exact fin15Anchored_clause21623 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21624 chi hbad
                ·
                  exact fin15Anchored_clause21625 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21626 chi hbad
                ·
                  exact fin15Anchored_clause21627 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21628 chi hbad
                ·
                  exact fin15Anchored_clause21629 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21630 chi hbad
                ·
                  exact fin15Anchored_clause21631 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21632 chi hbad
                ·
                  exact fin15Anchored_clause21633 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21634 chi hbad
                ·
                  exact fin15Anchored_clause21635 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21636 chi hbad
                ·
                  exact fin15Anchored_clause21637 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21638 chi hbad
                ·
                  exact fin15Anchored_clause21639 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21640 chi hbad
                ·
                  exact fin15Anchored_clause21641 chi hbad
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
                  exact fin15Anchored_clause21642 chi hbad
                ·
                  exact fin15Anchored_clause21643 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21644 chi hbad
                ·
                  exact fin15Anchored_clause21645 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21646 chi hbad
                ·
                  exact fin15Anchored_clause21647 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21648 chi hbad
                ·
                  exact fin15Anchored_clause21649 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21650 chi hbad
                ·
                  exact fin15Anchored_clause21651 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21652 chi hbad
                ·
                  exact fin15Anchored_clause21653 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21654 chi hbad
                ·
                  exact fin15Anchored_clause21655 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21656 chi hbad
                ·
                  exact fin15Anchored_clause21657 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21658 chi hbad
                ·
                  exact fin15Anchored_clause21659 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21660 chi hbad
                ·
                  exact fin15Anchored_clause21661 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21662 chi hbad
                ·
                  exact fin15Anchored_clause21663 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21664 chi hbad
                ·
                  exact fin15Anchored_clause21665 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21666 chi hbad
                ·
                  exact fin15Anchored_clause21667 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21668 chi hbad
                ·
                  exact fin15Anchored_clause21669 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21670 chi hbad
                ·
                  exact fin15Anchored_clause21671 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21672 chi hbad
                ·
                  exact fin15Anchored_clause21673 chi hbad
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
                  exact fin15Anchored_clause21674 chi hbad
                ·
                  exact fin15Anchored_clause21675 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21676 chi hbad
                ·
                  exact fin15Anchored_clause21677 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21678 chi hbad
                ·
                  exact fin15Anchored_clause21679 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21680 chi hbad
                ·
                  exact fin15Anchored_clause21681 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21682 chi hbad
                ·
                  exact fin15Anchored_clause21683 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21684 chi hbad
                ·
                  exact fin15Anchored_clause21685 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21686 chi hbad
                ·
                  exact fin15Anchored_clause21687 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21688 chi hbad
                ·
                  exact fin15Anchored_clause21689 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21690 chi hbad
                ·
                  exact fin15Anchored_clause21691 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21692 chi hbad
                ·
                  exact fin15Anchored_clause21693 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21694 chi hbad
                ·
                  exact fin15Anchored_clause21695 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21696 chi hbad
                ·
                  exact fin15Anchored_clause21697 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21698 chi hbad
                ·
                  exact fin15Anchored_clause21699 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21700 chi hbad
                ·
                  exact fin15Anchored_clause21701 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21702 chi hbad
                ·
                  exact fin15Anchored_clause21703 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21704 chi hbad
                ·
                  exact fin15Anchored_clause21705 chi hbad

end ErdosSzekeres

end
