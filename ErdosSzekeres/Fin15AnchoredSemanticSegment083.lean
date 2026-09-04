module

public import ErdosSzekeres.Fin15AnchoredClauseChunk163
public import ErdosSzekeres.Fin15AnchoredClauseChunk164
public import ErdosSzekeres.Fin15AnchoredClauseChunk165

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 083. -/

theorem fin15Anchored_rejectSemanticSegment083
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2972 chi ∧
      ¬Fin15AnchoredAtom1256 chi) ∨
      ((¬Fin15AnchoredAtom2972 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0854 chi ∧
      Fin15AnchoredAtom0872 chi ∧
      Fin15AnchoredAtom1036 chi ∧
      Fin15AnchoredAtom1256 chi) ∨
      (Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom0852 chi))) ∨
      (((Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom0855 chi) ∨
      (Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom0873 chi)) ∨
      ((Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom1037 chi) ∨
      (Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom1257 chi)))) ∨
      ((((¬Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1257 chi) ∨
      (Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom0852 chi)) ∨
      ((Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom0856 chi) ∨
      (Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom0874 chi))) ∨
      (((Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom1038 chi) ∨
      (Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom1258 chi)) ∨
      ((¬Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1258 chi) ∨
      (Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom0852 chi))))) ∨
      (((((Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom0857 chi) ∨
      (Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom0875 chi)) ∨
      ((Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom1039 chi) ∨
      (Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom1259 chi))) ∨
      (((¬Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1259 chi) ∨
      (Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom0853 chi)) ∨
      ((Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom0854 chi) ∨
      (Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom0876 chi)))) ∨
      ((((Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom1040 chi) ∨
      (Fin15AnchoredAtom2976 chi ∧
      ¬Fin15AnchoredAtom1260 chi)) ∨
      ((¬Fin15AnchoredAtom2976 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0854 chi ∧
      Fin15AnchoredAtom0876 chi ∧
      Fin15AnchoredAtom1040 chi ∧
      Fin15AnchoredAtom1260 chi) ∨
      (Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom0853 chi))) ∨
      (((Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom0855 chi) ∨
      (Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom0877 chi)) ∨
      ((Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom1041 chi) ∨
      (Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom1261 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1261 chi) ∨
      (Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom0853 chi)) ∨
      ((Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom0856 chi) ∨
      (Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom0878 chi))) ∨
      (((Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom1042 chi) ∨
      (Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom1262 chi)) ∨
      ((¬Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1262 chi) ∨
      (Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom0853 chi)))) ∨
      ((((Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom0857 chi) ∨
      (Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom0879 chi)) ∨
      ((Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom1043 chi) ∨
      (Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom1263 chi))) ∨
      (((¬Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1263 chi) ∨
      (Fin15AnchoredAtom2980 chi ∧
      ¬Fin15AnchoredAtom0855 chi)) ∨
      ((Fin15AnchoredAtom2980 chi ∧
      ¬Fin15AnchoredAtom1264 chi) ∨
      (¬Fin15AnchoredAtom2980 chi ∧
      Fin15AnchoredAtom0854 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0880 chi ∧
      Fin15AnchoredAtom1044 chi ∧
      Fin15AnchoredAtom1264 chi))))) ∨
      (((((Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom0855 chi) ∨
      (Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom0856 chi)) ∨
      ((Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom0883 chi) ∨
      (Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom1047 chi))) ∨
      (((Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom1267 chi) ∨
      (¬Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1267 chi)) ∨
      ((Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom0855 chi) ∨
      (Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom0857 chi)))) ∨
      ((((Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom0884 chi) ∨
      (Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom1048 chi)) ∨
      ((Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom1268 chi) ∨
      (¬Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1268 chi))) ∨
      (((Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom0856 chi) ∨
      (Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom0857 chi)) ∨
      ((Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom0885 chi) ∨
      (Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom1049 chi))))))) ∨
      ((((((Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom1269 chi) ∨
      ((¬Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1269 chi) ∨
      (Fin15AnchoredAtom2986 chi ∧
      ¬Fin15AnchoredAtom1050 chi))) ∨
      (((Fin15AnchoredAtom2987 chi ∧
      ¬Fin15AnchoredAtom1051 chi) ∨
      (Fin15AnchoredAtom2991 chi ∧
      ¬Fin15AnchoredAtom0864 chi)) ∨
      ((Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom0859 chi) ∨
      (Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom0860 chi)))) ∨
      ((((Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom0871 chi) ∨
      (Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom1056 chi)) ∨
      ((Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom1276 chi) ∨
      (¬Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1276 chi))) ∨
      (((Fin15AnchoredAtom2993 chi ∧
      ¬Fin15AnchoredAtom0859 chi) ∨
      (Fin15AnchoredAtom2993 chi ∧
      ¬Fin15AnchoredAtom1277 chi)) ∨
      ((Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom0859 chi) ∨
      (Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom0862 chi))))) ∨
      (((((Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom0873 chi) ∨
      (Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom1058 chi)) ∨
      ((Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom1278 chi) ∨
      (¬Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1278 chi))) ∨
      (((Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom0859 chi) ∨
      (Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom0863 chi)) ∨
      ((Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom0874 chi) ∨
      (Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom1059 chi)))) ∨
      ((((Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom1279 chi) ∨
      (¬Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1279 chi)) ∨
      ((Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom0859 chi) ∨
      (Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom0864 chi))) ∨
      (((Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom0875 chi) ∨
      (Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom1060 chi)) ∨
      ((Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom1280 chi) ∨
      (¬Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1280 chi)))))) ∨
      ((((((Fin15AnchoredAtom2997 chi ∧
      ¬Fin15AnchoredAtom0861 chi) ∨
      (Fin15AnchoredAtom2997 chi ∧
      ¬Fin15AnchoredAtom1281 chi)) ∨
      ((Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom0860 chi) ∨
      (Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom0862 chi))) ∨
      (((Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom0877 chi) ∨
      (Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom1062 chi)) ∨
      ((Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom1282 chi) ∨
      (¬Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1282 chi)))) ∨
      ((((Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom0860 chi) ∨
      (Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom0863 chi)) ∨
      ((Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom0878 chi) ∨
      (Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom1063 chi))) ∨
      (((Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom1283 chi) ∨
      (¬Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1283 chi)) ∨
      ((Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom0860 chi) ∨
      (Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom0864 chi))))) ∨
      (((((Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom0879 chi) ∨
      (Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom1064 chi)) ∨
      ((Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom1284 chi) ∨
      (¬Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1284 chi))) ∨
      (((Fin15AnchoredAtom3001 chi ∧
      ¬Fin15AnchoredAtom0862 chi) ∨
      (Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom0862 chi)) ∨
      ((Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom0863 chi) ∨
      (Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom0883 chi)))) ∨
      ((((Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom1068 chi) ∨
      (Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom1288 chi)) ∨
      ((¬Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1288 chi) ∨
      (Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom0862 chi))) ∨
      (((Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom0864 chi) ∨
      (Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom0884 chi)) ∨
      ((Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom1069 chi) ∨
      (Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom1289 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1289 chi) ∨
      ((Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom0863 chi) ∨
      (Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom0864 chi))) ∨
      (((Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom0885 chi) ∨
      (Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom1070 chi)) ∨
      ((Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom1290 chi) ∨
      (¬Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1290 chi)))) ∨
      ((((Fin15AnchoredAtom3007 chi ∧
      ¬Fin15AnchoredAtom1291 chi) ∨
      (Fin15AnchoredAtom3013 chi ∧
      ¬Fin15AnchoredAtom1297 chi)) ∨
      ((Fin15AnchoredAtom3014 chi ∧
      ¬Fin15AnchoredAtom1298 chi) ∨
      (Fin15AnchoredAtom3019 chi ∧
      ¬Fin15AnchoredAtom1303 chi))) ∨
      (((Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom0871 chi) ∨
      (Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom0872 chi)) ∨
      ((Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom0876 chi) ∨
      (Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom1086 chi))))) ∨
      (((((Fin15AnchoredAtom3022 chi ∧
      ¬Fin15AnchoredAtom1306 chi) ∨
      (¬Fin15AnchoredAtom3022 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0872 chi ∧
      Fin15AnchoredAtom0876 chi ∧
      Fin15AnchoredAtom1086 chi ∧
      Fin15AnchoredAtom1306 chi)) ∨
      ((Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom0871 chi) ∨
      (Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom0873 chi))) ∨
      (((Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom0877 chi) ∨
      (Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom1087 chi)) ∨
      ((Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom1307 chi) ∨
      (¬Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1307 chi)))) ∨
      ((((Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom0871 chi) ∨
      (Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom0874 chi)) ∨
      ((Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom0878 chi) ∨
      (Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom1088 chi))) ∨
      (((Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom1308 chi) ∨
      (¬Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1308 chi)) ∨
      ((Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom0871 chi) ∨
      (Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom0875 chi)))))) ∨
      ((((((Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom0879 chi) ∨
      (Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom1089 chi)) ∨
      ((Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom1309 chi) ∨
      (¬Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1309 chi))) ∨
      (((Fin15AnchoredAtom3026 chi ∧
      ¬Fin15AnchoredAtom0873 chi) ∨
      (Fin15AnchoredAtom3026 chi ∧
      ¬Fin15AnchoredAtom1090 chi)) ∨
      ((Fin15AnchoredAtom3026 chi ∧
      ¬Fin15AnchoredAtom1310 chi) ∨
      (¬Fin15AnchoredAtom3026 chi ∧
      Fin15AnchoredAtom0872 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0880 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1310 chi)))) ∨
      ((((Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom0873 chi) ∨
      (Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom0874 chi)) ∨
      ((Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom0883 chi) ∨
      (Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom1093 chi))) ∨
      (((Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom1313 chi) ∨
      (¬Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1313 chi)) ∨
      ((Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom0873 chi) ∨
      (Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom0875 chi))))) ∨
      (((((Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom0884 chi) ∨
      (Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom1094 chi)) ∨
      ((Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom1314 chi) ∨
      (¬Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1314 chi))) ∨
      (((Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom0874 chi) ∨
      (Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom0875 chi)) ∨
      ((Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom0885 chi) ∨
      (Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom1095 chi)))) ∨
      ((((Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom1315 chi) ∨
      (¬Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1315 chi)) ∨
      ((Fin15AnchoredAtom3032 chi ∧
      ¬Fin15AnchoredAtom1096 chi) ∨
      (Fin15AnchoredAtom3032 chi ∧
      ¬Fin15AnchoredAtom1316 chi))) ∨
      (((¬Fin15AnchoredAtom3032 chi ∧
      Fin15AnchoredAtom0876 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom0880 chi ∧
      Fin15AnchoredAtom1096 chi ∧
      Fin15AnchoredAtom1316 chi) ∨
      (Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom0877 chi)) ∨
      ((Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom0878 chi) ∨
      (Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom0883 chi))))))) ∨
      (((((((Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom1099 chi) ∨
      (Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom1319 chi)) ∨
      ((¬Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1319 chi) ∨
      (Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom0877 chi))) ∨
      (((Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom0879 chi) ∨
      (Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom0884 chi)) ∨
      ((Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom1100 chi) ∨
      (Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom1320 chi)))) ∨
      ((((¬Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1320 chi) ∨
      (Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom0878 chi)) ∨
      ((Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom0879 chi) ∨
      (Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom0885 chi))) ∨
      (((Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom1101 chi) ∨
      (Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom1321 chi)) ∨
      ((¬Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1321 chi) ∨
      (¬Fin15AnchoredAtom3038 chi ∧
      Fin15AnchoredAtom0880 chi ∧
      Fin15AnchoredAtom0881 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1102 chi ∧
      Fin15AnchoredAtom1322 chi))))) ∨
      (((((Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom0883 chi) ∨
      (Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom0884 chi)) ∨
      ((Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom0885 chi) ∨
      (Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom1105 chi))) ∨
      (((Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom1325 chi) ∨
      (¬Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1325 chi)) ∨
      ((Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom0886 chi) ∨
      (Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom0887 chi)))) ∨
      ((((Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom0941 chi)) ∨
      ((Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom1326 chi) ∨
      (¬Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom1326 chi))) ∨
      (((Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom0886 chi) ∨
      (Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom0888 chi)) ∨
      ((Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom0897 chi) ∨
      (Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom0942 chi)))))) ∨
      ((((((Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom1327 chi) ∨
      (¬Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom1327 chi)) ∨
      ((Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom0886 chi) ∨
      (Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom0889 chi))) ∨
      (((Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom0898 chi) ∨
      (Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom0943 chi)) ∨
      ((Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom1328 chi) ∨
      (¬Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom1328 chi)))) ∨
      ((((Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom0886 chi) ∨
      (Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom0890 chi)) ∨
      ((Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom0899 chi) ∨
      (Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom0944 chi))) ∨
      (((Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom1329 chi) ∨
      (¬Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom1329 chi)) ∨
      ((Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom0886 chi) ∨
      (Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom0891 chi))))) ∨
      (((((Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom0900 chi) ∨
      (Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom0945 chi)) ∨
      ((Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom1330 chi) ∨
      (¬Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom1330 chi))) ∨
      (((Fin15AnchoredAtom3047 chi ∧
      ¬Fin15AnchoredAtom0886 chi) ∨
      (Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom0886 chi)) ∨
      ((Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom0893 chi) ∨
      (Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom0902 chi)))) ∨
      ((((Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom0947 chi) ∨
      (Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom1332 chi)) ∨
      ((¬Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom1332 chi) ∨
      (Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom0886 chi))) ∨
      (((Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom0894 chi) ∨
      (Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom0903 chi)) ∨
      ((Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      (Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom1333 chi)))))))))) := by
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
                exact fin15Anchored_clause20948 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20949 chi hbad
                ·
                  exact fin15Anchored_clause20950 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20951 chi hbad
                ·
                  exact fin15Anchored_clause20952 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20953 chi hbad
                ·
                  exact fin15Anchored_clause20954 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20955 chi hbad
                ·
                  exact fin15Anchored_clause20956 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20957 chi hbad
                ·
                  exact fin15Anchored_clause20958 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20959 chi hbad
                ·
                  exact fin15Anchored_clause20960 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20961 chi hbad
                ·
                  exact fin15Anchored_clause20962 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20963 chi hbad
                ·
                  exact fin15Anchored_clause20964 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20965 chi hbad
                ·
                  exact fin15Anchored_clause20966 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20967 chi hbad
                ·
                  exact fin15Anchored_clause20968 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20969 chi hbad
                ·
                  exact fin15Anchored_clause20970 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20971 chi hbad
                ·
                  exact fin15Anchored_clause20972 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20973 chi hbad
                ·
                  exact fin15Anchored_clause20974 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20975 chi hbad
                ·
                  exact fin15Anchored_clause20976 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20977 chi hbad
                ·
                  exact fin15Anchored_clause20978 chi hbad
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
                  exact fin15Anchored_clause20979 chi hbad
                ·
                  exact fin15Anchored_clause20980 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20981 chi hbad
                ·
                  exact fin15Anchored_clause20982 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20983 chi hbad
                ·
                  exact fin15Anchored_clause20984 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20985 chi hbad
                ·
                  exact fin15Anchored_clause20986 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20987 chi hbad
                ·
                  exact fin15Anchored_clause20988 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20989 chi hbad
                ·
                  exact fin15Anchored_clause20990 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20991 chi hbad
                ·
                  exact fin15Anchored_clause20992 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20993 chi hbad
                ·
                  exact fin15Anchored_clause20994 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20995 chi hbad
                ·
                  exact fin15Anchored_clause20996 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20997 chi hbad
                ·
                  exact fin15Anchored_clause20998 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause20999 chi hbad
                ·
                  exact fin15Anchored_clause21000 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21001 chi hbad
                ·
                  exact fin15Anchored_clause21002 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21003 chi hbad
                ·
                  exact fin15Anchored_clause21004 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21005 chi hbad
                ·
                  exact fin15Anchored_clause21006 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21007 chi hbad
                ·
                  exact fin15Anchored_clause21008 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21009 chi hbad
                ·
                  exact fin15Anchored_clause21010 chi hbad
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
                exact fin15Anchored_clause21011 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21012 chi hbad
                ·
                  exact fin15Anchored_clause21013 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21014 chi hbad
                ·
                  exact fin15Anchored_clause21015 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21016 chi hbad
                ·
                  exact fin15Anchored_clause21017 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21018 chi hbad
                ·
                  exact fin15Anchored_clause21019 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21020 chi hbad
                ·
                  exact fin15Anchored_clause21021 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21022 chi hbad
                ·
                  exact fin15Anchored_clause21023 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21024 chi hbad
                ·
                  exact fin15Anchored_clause21025 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21026 chi hbad
                ·
                  exact fin15Anchored_clause21027 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21028 chi hbad
                ·
                  exact fin15Anchored_clause21029 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21030 chi hbad
                ·
                  exact fin15Anchored_clause21031 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21032 chi hbad
                ·
                  exact fin15Anchored_clause21033 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21034 chi hbad
                ·
                  exact fin15Anchored_clause21035 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21036 chi hbad
                ·
                  exact fin15Anchored_clause21037 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21038 chi hbad
                ·
                  exact fin15Anchored_clause21039 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21040 chi hbad
                ·
                  exact fin15Anchored_clause21041 chi hbad
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
                  exact fin15Anchored_clause21042 chi hbad
                ·
                  exact fin15Anchored_clause21043 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21044 chi hbad
                ·
                  exact fin15Anchored_clause21045 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21046 chi hbad
                ·
                  exact fin15Anchored_clause21047 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21048 chi hbad
                ·
                  exact fin15Anchored_clause21049 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21050 chi hbad
                ·
                  exact fin15Anchored_clause21051 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21052 chi hbad
                ·
                  exact fin15Anchored_clause21053 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21054 chi hbad
                ·
                  exact fin15Anchored_clause21055 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21056 chi hbad
                ·
                  exact fin15Anchored_clause21057 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21058 chi hbad
                ·
                  exact fin15Anchored_clause21059 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21060 chi hbad
                ·
                  exact fin15Anchored_clause21061 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21062 chi hbad
                ·
                  exact fin15Anchored_clause21063 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21064 chi hbad
                ·
                  exact fin15Anchored_clause21065 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21066 chi hbad
                ·
                  exact fin15Anchored_clause21067 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21068 chi hbad
                ·
                  exact fin15Anchored_clause21069 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21070 chi hbad
                ·
                  exact fin15Anchored_clause21071 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21072 chi hbad
                ·
                  exact fin15Anchored_clause21073 chi hbad
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
                exact fin15Anchored_clause21074 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21075 chi hbad
                ·
                  exact fin15Anchored_clause21076 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21077 chi hbad
                ·
                  exact fin15Anchored_clause21078 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21079 chi hbad
                ·
                  exact fin15Anchored_clause21080 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21081 chi hbad
                ·
                  exact fin15Anchored_clause21082 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21083 chi hbad
                ·
                  exact fin15Anchored_clause21084 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21085 chi hbad
                ·
                  exact fin15Anchored_clause21086 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21087 chi hbad
                ·
                  exact fin15Anchored_clause21088 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21089 chi hbad
                ·
                  exact fin15Anchored_clause21090 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21091 chi hbad
                ·
                  exact fin15Anchored_clause21092 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21093 chi hbad
                ·
                  exact fin15Anchored_clause21094 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21095 chi hbad
                ·
                  exact fin15Anchored_clause21096 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21097 chi hbad
                ·
                  exact fin15Anchored_clause21098 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21099 chi hbad
                ·
                  exact fin15Anchored_clause21100 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21101 chi hbad
                ·
                  exact fin15Anchored_clause21102 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21103 chi hbad
                ·
                  exact fin15Anchored_clause21104 chi hbad
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
                  exact fin15Anchored_clause21105 chi hbad
                ·
                  exact fin15Anchored_clause21106 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21107 chi hbad
                ·
                  exact fin15Anchored_clause21108 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21109 chi hbad
                ·
                  exact fin15Anchored_clause21110 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21111 chi hbad
                ·
                  exact fin15Anchored_clause21112 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21113 chi hbad
                ·
                  exact fin15Anchored_clause21114 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21115 chi hbad
                ·
                  exact fin15Anchored_clause21116 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21117 chi hbad
                ·
                  exact fin15Anchored_clause21118 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21119 chi hbad
                ·
                  exact fin15Anchored_clause21120 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21121 chi hbad
                ·
                  exact fin15Anchored_clause21122 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21123 chi hbad
                ·
                  exact fin15Anchored_clause21124 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21125 chi hbad
                ·
                  exact fin15Anchored_clause21126 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21127 chi hbad
                ·
                  exact fin15Anchored_clause21128 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21129 chi hbad
                ·
                  exact fin15Anchored_clause21130 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21131 chi hbad
                ·
                  exact fin15Anchored_clause21132 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21133 chi hbad
                ·
                  exact fin15Anchored_clause21134 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21135 chi hbad
                ·
                  exact fin15Anchored_clause21136 chi hbad
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
                  exact fin15Anchored_clause21137 chi hbad
                ·
                  exact fin15Anchored_clause21138 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21139 chi hbad
                ·
                  exact fin15Anchored_clause21140 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21141 chi hbad
                ·
                  exact fin15Anchored_clause21142 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21143 chi hbad
                ·
                  exact fin15Anchored_clause21144 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21145 chi hbad
                ·
                  exact fin15Anchored_clause21146 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21147 chi hbad
                ·
                  exact fin15Anchored_clause21148 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21149 chi hbad
                ·
                  exact fin15Anchored_clause21150 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21151 chi hbad
                ·
                  exact fin15Anchored_clause21152 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21153 chi hbad
                ·
                  exact fin15Anchored_clause21154 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21155 chi hbad
                ·
                  exact fin15Anchored_clause21156 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21157 chi hbad
                ·
                  exact fin15Anchored_clause21158 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21159 chi hbad
                ·
                  exact fin15Anchored_clause21160 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21161 chi hbad
                ·
                  exact fin15Anchored_clause21162 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21163 chi hbad
                ·
                  exact fin15Anchored_clause21164 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21165 chi hbad
                ·
                  exact fin15Anchored_clause21166 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21167 chi hbad
                ·
                  exact fin15Anchored_clause21168 chi hbad
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
                  exact fin15Anchored_clause21169 chi hbad
                ·
                  exact fin15Anchored_clause21170 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21171 chi hbad
                ·
                  exact fin15Anchored_clause21172 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21173 chi hbad
                ·
                  exact fin15Anchored_clause21174 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21175 chi hbad
                ·
                  exact fin15Anchored_clause21176 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21177 chi hbad
                ·
                  exact fin15Anchored_clause21178 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21179 chi hbad
                ·
                  exact fin15Anchored_clause21180 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21181 chi hbad
                ·
                  exact fin15Anchored_clause21182 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21183 chi hbad
                ·
                  exact fin15Anchored_clause21184 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21185 chi hbad
                ·
                  exact fin15Anchored_clause21186 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21187 chi hbad
                ·
                  exact fin15Anchored_clause21188 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21189 chi hbad
                ·
                  exact fin15Anchored_clause21190 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21191 chi hbad
                ·
                  exact fin15Anchored_clause21192 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21193 chi hbad
                ·
                  exact fin15Anchored_clause21194 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21195 chi hbad
                ·
                  exact fin15Anchored_clause21196 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21197 chi hbad
                ·
                  exact fin15Anchored_clause21198 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21199 chi hbad
                ·
                  exact fin15Anchored_clause21200 chi hbad

end ErdosSzekeres

end
