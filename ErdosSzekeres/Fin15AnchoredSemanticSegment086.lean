module

public import ErdosSzekeres.Fin15AnchoredClauseChunk169
public import ErdosSzekeres.Fin15AnchoredClauseChunk170
public import ErdosSzekeres.Fin15AnchoredClauseChunk171

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 086. -/

theorem fin15Anchored_rejectSemanticSegment086
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom0913 chi) ∨
      ((Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom0917 chi) ∨
      (Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom1053 chi))) ∨
      (((Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom1438 chi) ∨
      (¬Fin15AnchoredAtom3154 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1438 chi)) ∨
      ((Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom0913 chi) ∨
      (Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom0918 chi)))) ∨
      ((((Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom0924 chi) ∨
      (Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom1054 chi)) ∨
      ((Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom1439 chi) ∨
      (¬Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1439 chi))) ∨
      (((Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom0913 chi) ∨
      (Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom0919 chi)) ∨
      ((Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom1055 chi) ∨
      (Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom1440 chi))))) ∨
      (((((¬Fin15AnchoredAtom3156 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1440 chi) ∨
      (Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom0914 chi)) ∨
      ((Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom0915 chi) ∨
      (Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom0926 chi))) ∨
      (((Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom1441 chi)) ∨
      ((¬Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1441 chi) ∨
      (Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom0914 chi)))) ∨
      ((((Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom0927 chi) ∨
      (Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom1442 chi)) ∨
      ((Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom0914 chi) ∨
      (Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom0917 chi))) ∨
      (((Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom0928 chi) ∨
      (Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom1058 chi)) ∨
      ((Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom1443 chi) ∨
      (¬Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1443 chi)))))) ∨
      ((((((Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom0914 chi) ∨
      (Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom0918 chi)) ∨
      ((Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom0929 chi) ∨
      (Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom1059 chi))) ∨
      (((Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom1444 chi) ∨
      (¬Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1444 chi)) ∨
      ((Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom0914 chi) ∨
      (Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom0919 chi)))) ∨
      ((((Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom0930 chi) ∨
      (Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom1060 chi)) ∨
      ((Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom1445 chi) ∨
      (¬Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1445 chi))) ∨
      (((Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom0915 chi) ∨
      (Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom0916 chi)) ∨
      ((Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom1061 chi) ∨
      (Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom0915 chi))))) ∨
      (((((Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom0917 chi) ∨
      (Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom0932 chi)) ∨
      ((Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom1062 chi) ∨
      (Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom1447 chi))) ∨
      (((¬Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1447 chi) ∨
      (Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom0915 chi)) ∨
      ((Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom0918 chi) ∨
      (Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom0933 chi)))) ∨
      ((((Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom1063 chi) ∨
      (Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom1448 chi)) ∨
      ((¬Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1448 chi) ∨
      (Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom0915 chi))) ∨
      (((Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom0919 chi) ∨
      (Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom0934 chi)) ∨
      ((Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom1064 chi) ∨
      (Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom1449 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1449 chi) ∨
      ((Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom0917 chi) ∨
      (Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom0935 chi))) ∨
      (((Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom1065 chi) ∨
      (Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom1450 chi)) ∨
      ((Fin15AnchoredAtom3167 chi ∧
      ¬Fin15AnchoredAtom0918 chi) ∨
      (Fin15AnchoredAtom3168 chi ∧
      ¬Fin15AnchoredAtom0937 chi)))) ∨
      ((((Fin15AnchoredAtom3168 chi ∧
      ¬Fin15AnchoredAtom1067 chi) ∨
      (Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom0917 chi)) ∨
      ((Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom0918 chi) ∨
      (Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom0938 chi))) ∨
      (((Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom1068 chi) ∨
      (Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom1453 chi)) ∨
      ((¬Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1453 chi) ∨
      (Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom0917 chi))))) ∨
      (((((Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom0919 chi) ∨
      (Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom0939 chi)) ∨
      ((Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom1069 chi) ∨
      (Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom1454 chi))) ∨
      (((¬Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1454 chi) ∨
      (Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom0918 chi)) ∨
      ((Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom0919 chi) ∨
      (Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom0940 chi)))) ∨
      ((((Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom1070 chi) ∨
      (Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom1455 chi)) ∨
      ((¬Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1455 chi) ∨
      (Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom0920 chi))) ∨
      (((Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom0921 chi) ∨
      (Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom0926 chi)) ∨
      ((Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom1071 chi) ∨
      (Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom1456 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3172 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1456 chi) ∨
      (Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom0920 chi)) ∨
      ((Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom0923 chi) ∨
      (Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom0928 chi))) ∨
      (((Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom1073 chi) ∨
      (Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom1458 chi)) ∨
      ((¬Fin15AnchoredAtom3174 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1458 chi) ∨
      (Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom0920 chi)))) ∨
      ((((Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom0924 chi) ∨
      (Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom0929 chi)) ∨
      ((Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom1074 chi) ∨
      (Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom1459 chi))) ∨
      (((¬Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1459 chi) ∨
      (Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom0920 chi)) ∨
      ((Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom0925 chi) ∨
      (Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom0930 chi))))) ∨
      (((((Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom1075 chi) ∨
      (Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom1460 chi)) ∨
      ((¬Fin15AnchoredAtom3176 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom1075 chi ∧
      Fin15AnchoredAtom1460 chi) ∨
      (Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom0921 chi))) ∨
      (((Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom0923 chi) ∨
      (Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom0932 chi)) ∨
      ((Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom1077 chi) ∨
      (Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom1462 chi)))) ∨
      ((((¬Fin15AnchoredAtom3178 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1462 chi) ∨
      (Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom0921 chi)) ∨
      ((Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom0924 chi) ∨
      (Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom0933 chi))) ∨
      (((Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom1078 chi) ∨
      (Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom1463 chi)) ∨
      ((¬Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1463 chi) ∨
      (Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom0921 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom0934 chi) ∨
      ((Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom1079 chi) ∨
      (Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom1464 chi))) ∨
      (((¬Fin15AnchoredAtom3180 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1079 chi ∧
      Fin15AnchoredAtom1464 chi) ∨
      (Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom0923 chi)) ∨
      ((Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom0924 chi) ∨
      (Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom0938 chi)))) ∨
      ((((Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom1083 chi) ∨
      (Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom1468 chi)) ∨
      ((¬Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1468 chi) ∨
      (Fin15AnchoredAtom3185 chi ∧
      ¬Fin15AnchoredAtom0923 chi))) ∨
      (((Fin15AnchoredAtom3185 chi ∧
      ¬Fin15AnchoredAtom0939 chi) ∨
      (Fin15AnchoredAtom3185 chi ∧
      ¬Fin15AnchoredAtom1084 chi)) ∨
      ((¬Fin15AnchoredAtom3185 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1469 chi) ∨
      (Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom0924 chi))))) ∨
      (((((Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom0940 chi) ∨
      (Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom1085 chi)) ∨
      ((Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom1470 chi) ∨
      (¬Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1470 chi))) ∨
      (((Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom0926 chi) ∨
      (Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom1086 chi)) ∨
      ((Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom1471 chi) ∨
      (Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom0926 chi)))) ∨
      ((((Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom0928 chi) ∨
      (Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom0932 chi)) ∨
      ((Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom1087 chi) ∨
      (Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom1472 chi))) ∨
      (((¬Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1472 chi) ∨
      (Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom0926 chi)) ∨
      ((Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom0929 chi) ∨
      (Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom0933 chi)))))) ∨
      ((((((Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom1088 chi) ∨
      (Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom1473 chi)) ∨
      ((¬Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1473 chi) ∨
      (Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom0926 chi))) ∨
      (((Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom0930 chi) ∨
      (Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom0934 chi)) ∨
      ((Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom1089 chi) ∨
      (Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom1474 chi)))) ∨
      ((((¬Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1474 chi) ∨
      (Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom0928 chi)) ∨
      ((Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom0935 chi) ∨
      (Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom1090 chi))) ∨
      (((Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom1475 chi) ∨
      (¬Fin15AnchoredAtom3191 chi ∧
      Fin15AnchoredAtom0927 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom0935 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1475 chi)) ∨
      ((Fin15AnchoredAtom3192 chi ∧
      ¬Fin15AnchoredAtom0929 chi) ∨
      (¬Fin15AnchoredAtom3192 chi ∧
      Fin15AnchoredAtom0927 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom0936 chi ∧
      Fin15AnchoredAtom1091 chi ∧
      Fin15AnchoredAtom1476 chi))))) ∨
      (((((Fin15AnchoredAtom3193 chi ∧
      ¬Fin15AnchoredAtom0930 chi) ∨
      (Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom0928 chi)) ∨
      ((Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom0929 chi) ∨
      (Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom0938 chi))) ∨
      (((Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom1093 chi) ∨
      (Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom1478 chi)) ∨
      ((¬Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1478 chi) ∨
      (Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom0928 chi)))) ∨
      ((((Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom0930 chi) ∨
      (Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom0939 chi)) ∨
      ((Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom1094 chi) ∨
      (Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom1479 chi))) ∨
      (((¬Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1479 chi) ∨
      (Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom0929 chi)) ∨
      ((Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom0930 chi) ∨
      (Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom0940 chi))))))) ∨
      ((((((Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom1095 chi) ∨
      ((Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom1480 chi) ∨
      (¬Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1480 chi))) ∨
      (((Fin15AnchoredAtom3197 chi ∧
      ¬Fin15AnchoredAtom0932 chi) ∨
      (Fin15AnchoredAtom3197 chi ∧
      ¬Fin15AnchoredAtom1096 chi)) ∨
      ((Fin15AnchoredAtom3198 chi ∧
      ¬Fin15AnchoredAtom0933 chi) ∨
      (Fin15AnchoredAtom3198 chi ∧
      ¬Fin15AnchoredAtom0936 chi)))) ∨
      ((((Fin15AnchoredAtom3199 chi ∧
      ¬Fin15AnchoredAtom0934 chi) ∨
      (Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom0932 chi)) ∨
      ((Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom0933 chi) ∨
      (Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom0938 chi))) ∨
      (((Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom1099 chi) ∨
      (Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom1484 chi)) ∨
      ((¬Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1484 chi) ∨
      (Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom0932 chi))))) ∨
      (((((Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom0934 chi) ∨
      (Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom0939 chi)) ∨
      ((Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom1100 chi) ∨
      (Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom1485 chi))) ∨
      (((¬Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1485 chi) ∨
      (Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom0933 chi)) ∨
      ((Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom0934 chi) ∨
      (Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom0940 chi)))) ∨
      ((((Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom1101 chi) ∨
      (Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom1486 chi)) ∨
      ((¬Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1486 chi) ∨
      (Fin15AnchoredAtom3203 chi ∧
      ¬Fin15AnchoredAtom0938 chi))) ∨
      (((Fin15AnchoredAtom3204 chi ∧
      ¬Fin15AnchoredAtom0939 chi) ∨
      (Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom0938 chi)) ∨
      ((Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom0939 chi) ∨
      (Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom0940 chi)))))) ∨
      ((((((Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom1105 chi) ∨
      (Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom1490 chi)) ∨
      ((¬Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1490 chi) ∨
      (Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom0941 chi))) ∨
      (((Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom0942 chi) ∨
      (Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom0950 chi)) ∨
      ((Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom0986 chi) ∨
      (Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom1491 chi)))) ∨
      ((((¬Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom1491 chi) ∨
      (Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom0941 chi)) ∨
      ((Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom0943 chi) ∨
      (Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom0951 chi))) ∨
      (((Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom0987 chi) ∨
      (Fin15AnchoredAtom3208 chi ∧
      ¬Fin15AnchoredAtom1492 chi)) ∨
      ((¬Fin15AnchoredAtom3208 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom1492 chi) ∨
      (Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom0941 chi))))) ∨
      (((((Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom0944 chi) ∨
      (Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom0952 chi)) ∨
      ((Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom0988 chi) ∨
      (Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom1493 chi))) ∨
      (((¬Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom1493 chi) ∨
      (Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom0941 chi)) ∨
      ((Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom0945 chi) ∨
      (Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom0953 chi)))) ∨
      ((((Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom0989 chi) ∨
      (Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom1494 chi)) ∨
      ((¬Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom1494 chi) ∨
      (Fin15AnchoredAtom3211 chi ∧
      ¬Fin15AnchoredAtom1495 chi))) ∨
      (((Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom0941 chi) ∨
      (Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom0947 chi)) ∨
      ((Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom0991 chi)))))))))) := by
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
                exact fin15Anchored_clause21706 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21707 chi hbad
                ·
                  exact fin15Anchored_clause21708 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21709 chi hbad
                ·
                  exact fin15Anchored_clause21710 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21711 chi hbad
                ·
                  exact fin15Anchored_clause21712 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21713 chi hbad
                ·
                  exact fin15Anchored_clause21714 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21715 chi hbad
                ·
                  exact fin15Anchored_clause21716 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21717 chi hbad
                ·
                  exact fin15Anchored_clause21718 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21719 chi hbad
                ·
                  exact fin15Anchored_clause21720 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21721 chi hbad
                ·
                  exact fin15Anchored_clause21722 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21723 chi hbad
                ·
                  exact fin15Anchored_clause21724 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21725 chi hbad
                ·
                  exact fin15Anchored_clause21726 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21727 chi hbad
                ·
                  exact fin15Anchored_clause21728 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21729 chi hbad
                ·
                  exact fin15Anchored_clause21730 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21731 chi hbad
                ·
                  exact fin15Anchored_clause21732 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21733 chi hbad
                ·
                  exact fin15Anchored_clause21734 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21735 chi hbad
                ·
                  exact fin15Anchored_clause21736 chi hbad
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
                  exact fin15Anchored_clause21737 chi hbad
                ·
                  exact fin15Anchored_clause21738 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21739 chi hbad
                ·
                  exact fin15Anchored_clause21740 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21741 chi hbad
                ·
                  exact fin15Anchored_clause21742 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21743 chi hbad
                ·
                  exact fin15Anchored_clause21744 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21745 chi hbad
                ·
                  exact fin15Anchored_clause21746 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21747 chi hbad
                ·
                  exact fin15Anchored_clause21748 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21749 chi hbad
                ·
                  exact fin15Anchored_clause21750 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21751 chi hbad
                ·
                  exact fin15Anchored_clause21752 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21753 chi hbad
                ·
                  exact fin15Anchored_clause21754 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21755 chi hbad
                ·
                  exact fin15Anchored_clause21756 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21757 chi hbad
                ·
                  exact fin15Anchored_clause21758 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21759 chi hbad
                ·
                  exact fin15Anchored_clause21760 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21761 chi hbad
                ·
                  exact fin15Anchored_clause21762 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21763 chi hbad
                ·
                  exact fin15Anchored_clause21764 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21765 chi hbad
                ·
                  exact fin15Anchored_clause21766 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21767 chi hbad
                ·
                  exact fin15Anchored_clause21768 chi hbad
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
                exact fin15Anchored_clause21769 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21770 chi hbad
                ·
                  exact fin15Anchored_clause21771 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21772 chi hbad
                ·
                  exact fin15Anchored_clause21773 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21774 chi hbad
                ·
                  exact fin15Anchored_clause21775 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21776 chi hbad
                ·
                  exact fin15Anchored_clause21777 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21778 chi hbad
                ·
                  exact fin15Anchored_clause21779 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21780 chi hbad
                ·
                  exact fin15Anchored_clause21781 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21782 chi hbad
                ·
                  exact fin15Anchored_clause21783 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21784 chi hbad
                ·
                  exact fin15Anchored_clause21785 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21786 chi hbad
                ·
                  exact fin15Anchored_clause21787 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21788 chi hbad
                ·
                  exact fin15Anchored_clause21789 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21790 chi hbad
                ·
                  exact fin15Anchored_clause21791 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21792 chi hbad
                ·
                  exact fin15Anchored_clause21793 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21794 chi hbad
                ·
                  exact fin15Anchored_clause21795 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21796 chi hbad
                ·
                  exact fin15Anchored_clause21797 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21798 chi hbad
                ·
                  exact fin15Anchored_clause21799 chi hbad
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
                  exact fin15Anchored_clause21800 chi hbad
                ·
                  exact fin15Anchored_clause21801 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21802 chi hbad
                ·
                  exact fin15Anchored_clause21803 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21804 chi hbad
                ·
                  exact fin15Anchored_clause21805 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21806 chi hbad
                ·
                  exact fin15Anchored_clause21807 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21808 chi hbad
                ·
                  exact fin15Anchored_clause21809 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21810 chi hbad
                ·
                  exact fin15Anchored_clause21811 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21812 chi hbad
                ·
                  exact fin15Anchored_clause21813 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21814 chi hbad
                ·
                  exact fin15Anchored_clause21815 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21816 chi hbad
                ·
                  exact fin15Anchored_clause21817 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21818 chi hbad
                ·
                  exact fin15Anchored_clause21819 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21820 chi hbad
                ·
                  exact fin15Anchored_clause21821 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21822 chi hbad
                ·
                  exact fin15Anchored_clause21823 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21824 chi hbad
                ·
                  exact fin15Anchored_clause21825 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21826 chi hbad
                ·
                  exact fin15Anchored_clause21827 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21828 chi hbad
                ·
                  exact fin15Anchored_clause21829 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21830 chi hbad
                ·
                  exact fin15Anchored_clause21831 chi hbad
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
                exact fin15Anchored_clause21832 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21833 chi hbad
                ·
                  exact fin15Anchored_clause21834 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21835 chi hbad
                ·
                  exact fin15Anchored_clause21836 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21837 chi hbad
                ·
                  exact fin15Anchored_clause21838 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21839 chi hbad
                ·
                  exact fin15Anchored_clause21840 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21841 chi hbad
                ·
                  exact fin15Anchored_clause21842 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21843 chi hbad
                ·
                  exact fin15Anchored_clause21844 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21845 chi hbad
                ·
                  exact fin15Anchored_clause21846 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21847 chi hbad
                ·
                  exact fin15Anchored_clause21848 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21849 chi hbad
                ·
                  exact fin15Anchored_clause21850 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21851 chi hbad
                ·
                  exact fin15Anchored_clause21852 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21853 chi hbad
                ·
                  exact fin15Anchored_clause21854 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21855 chi hbad
                ·
                  exact fin15Anchored_clause21856 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21857 chi hbad
                ·
                  exact fin15Anchored_clause21858 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21859 chi hbad
                ·
                  exact fin15Anchored_clause21860 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21861 chi hbad
                ·
                  exact fin15Anchored_clause21862 chi hbad
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
                  exact fin15Anchored_clause21863 chi hbad
                ·
                  exact fin15Anchored_clause21864 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21865 chi hbad
                ·
                  exact fin15Anchored_clause21866 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21867 chi hbad
                ·
                  exact fin15Anchored_clause21868 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21869 chi hbad
                ·
                  exact fin15Anchored_clause21870 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21871 chi hbad
                ·
                  exact fin15Anchored_clause21872 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21873 chi hbad
                ·
                  exact fin15Anchored_clause21874 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21875 chi hbad
                ·
                  exact fin15Anchored_clause21876 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21877 chi hbad
                ·
                  exact fin15Anchored_clause21878 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21879 chi hbad
                ·
                  exact fin15Anchored_clause21880 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21881 chi hbad
                ·
                  exact fin15Anchored_clause21882 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21883 chi hbad
                ·
                  exact fin15Anchored_clause21884 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21885 chi hbad
                ·
                  exact fin15Anchored_clause21886 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21887 chi hbad
                ·
                  exact fin15Anchored_clause21888 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21889 chi hbad
                ·
                  exact fin15Anchored_clause21890 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21891 chi hbad
                ·
                  exact fin15Anchored_clause21892 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21893 chi hbad
                ·
                  exact fin15Anchored_clause21894 chi hbad
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
                exact fin15Anchored_clause21895 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21896 chi hbad
                ·
                  exact fin15Anchored_clause21897 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21898 chi hbad
                ·
                  exact fin15Anchored_clause21899 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21900 chi hbad
                ·
                  exact fin15Anchored_clause21901 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21902 chi hbad
                ·
                  exact fin15Anchored_clause21903 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21904 chi hbad
                ·
                  exact fin15Anchored_clause21905 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21906 chi hbad
                ·
                  exact fin15Anchored_clause21907 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21908 chi hbad
                ·
                  exact fin15Anchored_clause21909 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21910 chi hbad
                ·
                  exact fin15Anchored_clause21911 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21912 chi hbad
                ·
                  exact fin15Anchored_clause21913 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21914 chi hbad
                ·
                  exact fin15Anchored_clause21915 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21916 chi hbad
                ·
                  exact fin15Anchored_clause21917 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21918 chi hbad
                ·
                  exact fin15Anchored_clause21919 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21920 chi hbad
                ·
                  exact fin15Anchored_clause21921 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21922 chi hbad
                ·
                  exact fin15Anchored_clause21923 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21924 chi hbad
                ·
                  exact fin15Anchored_clause21925 chi hbad
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
                  exact fin15Anchored_clause21926 chi hbad
                ·
                  exact fin15Anchored_clause21927 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21928 chi hbad
                ·
                  exact fin15Anchored_clause21929 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21930 chi hbad
                ·
                  exact fin15Anchored_clause21931 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21932 chi hbad
                ·
                  exact fin15Anchored_clause21933 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21934 chi hbad
                ·
                  exact fin15Anchored_clause21935 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21936 chi hbad
                ·
                  exact fin15Anchored_clause21937 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21938 chi hbad
                ·
                  exact fin15Anchored_clause21939 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21940 chi hbad
                ·
                  exact fin15Anchored_clause21941 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21942 chi hbad
                ·
                  exact fin15Anchored_clause21943 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21944 chi hbad
                ·
                  exact fin15Anchored_clause21945 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21946 chi hbad
                ·
                  exact fin15Anchored_clause21947 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21948 chi hbad
                ·
                  exact fin15Anchored_clause21949 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21950 chi hbad
                ·
                  exact fin15Anchored_clause21951 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21952 chi hbad
                ·
                  exact fin15Anchored_clause21953 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21954 chi hbad
                ·
                  exact fin15Anchored_clause21955 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21956 chi hbad
                ·
                  exact fin15Anchored_clause21957 chi hbad

end ErdosSzekeres

end
