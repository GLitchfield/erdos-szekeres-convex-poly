module

public import ErdosSzekeres.Fin15AnchoredClauseChunk165
public import ErdosSzekeres.Fin15AnchoredClauseChunk166
public import ErdosSzekeres.Fin15AnchoredClauseChunk167

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 084. -/

theorem fin15Anchored_rejectSemanticSegment084
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom1333 chi) ∨
      ((Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom0886 chi) ∨
      (Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom0895 chi))) ∨
      (((Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom0904 chi) ∨
      (Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom0949 chi)) ∨
      ((Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom1334 chi) ∨
      (¬Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom1334 chi)))) ∨
      ((((Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom0887 chi) ∨
      (Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom0888 chi)) ∨
      ((Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom0905 chi) ∨
      (Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom0950 chi))) ∨
      (((Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom1335 chi) ∨
      (¬Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom1335 chi)) ∨
      ((Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom0887 chi) ∨
      (Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom0889 chi))))) ∨
      (((((Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom0906 chi) ∨
      (Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom0951 chi)) ∨
      ((Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom1336 chi) ∨
      (¬Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom1336 chi))) ∨
      (((Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom0887 chi) ∨
      (Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom0890 chi)) ∨
      ((Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom0907 chi) ∨
      (Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom0952 chi)))) ∨
      ((((Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom1337 chi) ∨
      (¬Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom1337 chi)) ∨
      ((Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom0887 chi) ∨
      (Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom0891 chi))) ∨
      (((Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom0908 chi) ∨
      (Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom0953 chi)) ∨
      ((Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom1338 chi) ∨
      (¬Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom1338 chi)))))) ∨
      ((((((Fin15AnchoredAtom3055 chi ∧
      ¬Fin15AnchoredAtom0887 chi) ∨
      (Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom0887 chi)) ∨
      ((Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom0893 chi) ∨
      (Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom0910 chi))) ∨
      (((Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom1340 chi)) ∨
      ((¬Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom1340 chi) ∨
      (Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom0887 chi)))) ∨
      ((((Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom0894 chi) ∨
      (Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom0911 chi)) ∨
      ((Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom0956 chi) ∨
      (Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom1341 chi))) ∨
      (((¬Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom1341 chi) ∨
      (Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom0887 chi)) ∨
      ((Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom0895 chi) ∨
      (Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom0912 chi))))) ∨
      (((((Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom0957 chi) ∨
      (Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom1342 chi)) ∨
      ((¬Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom1342 chi) ∨
      (Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom0888 chi))) ∨
      (((Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom0889 chi) ∨
      (Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom0913 chi)) ∨
      ((Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom0958 chi) ∨
      (Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom1343 chi)))) ∨
      ((((¬Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom1343 chi) ∨
      (Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom0888 chi)) ∨
      ((Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom0890 chi) ∨
      (Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom0914 chi))) ∨
      (((Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom0959 chi) ∨
      (Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom1344 chi)) ∨
      ((¬Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom1344 chi) ∨
      (Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom0888 chi))))))) ∨
      ((((((Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom0891 chi) ∨
      ((Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom0915 chi) ∨
      (Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom0960 chi))) ∨
      (((Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom1345 chi) ∨
      (¬Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom1345 chi)) ∨
      ((Fin15AnchoredAtom3062 chi ∧
      ¬Fin15AnchoredAtom0888 chi) ∨
      (Fin15AnchoredAtom3062 chi ∧
      ¬Fin15AnchoredAtom0892 chi)))) ∨
      ((((Fin15AnchoredAtom3062 chi ∧
      ¬Fin15AnchoredAtom0961 chi) ∨
      (Fin15AnchoredAtom3062 chi ∧
      ¬Fin15AnchoredAtom1346 chi)) ∨
      ((Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom0888 chi) ∨
      (Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom0893 chi))) ∨
      (((Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom0917 chi) ∨
      (Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom0962 chi)) ∨
      ((Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom1347 chi) ∨
      (¬Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom1347 chi))))) ∨
      (((((Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom0888 chi) ∨
      (Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom0894 chi)) ∨
      ((Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom0918 chi) ∨
      (Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom0963 chi))) ∨
      (((Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom1348 chi) ∨
      (¬Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom1348 chi)) ∨
      ((Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom0888 chi) ∨
      (Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom0895 chi)))) ∨
      ((((Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom0919 chi) ∨
      (Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom0964 chi)) ∨
      ((Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom1349 chi) ∨
      (¬Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom1349 chi))) ∨
      (((Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom0889 chi) ∨
      (Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom0890 chi)) ∨
      ((Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom0920 chi) ∨
      (Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom1350 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3066 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom1350 chi) ∨
      (Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom0889 chi)) ∨
      ((Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom0891 chi) ∨
      (Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom0921 chi))) ∨
      (((Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom0966 chi) ∨
      (Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom1351 chi)) ∨
      ((¬Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom1351 chi) ∨
      (Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom0889 chi)))) ∨
      ((((Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom0893 chi) ∨
      (Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom0968 chi)) ∨
      ((Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom1353 chi) ∨
      (¬Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom1353 chi))) ∨
      (((Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom0889 chi) ∨
      (Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom0894 chi)) ∨
      ((Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom0924 chi) ∨
      (Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom0969 chi))))) ∨
      (((((Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom1354 chi) ∨
      (¬Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom1354 chi)) ∨
      ((Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom0889 chi) ∨
      (Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom0895 chi))) ∨
      (((Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom0925 chi) ∨
      (Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom0970 chi)) ∨
      ((Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom1355 chi) ∨
      (¬Fin15AnchoredAtom3071 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom1355 chi)))) ∨
      ((((Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom0890 chi) ∨
      (Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom0891 chi)) ∨
      ((Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom0926 chi) ∨
      (Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom0971 chi))) ∨
      (((Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom1356 chi) ∨
      (¬Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1356 chi)) ∨
      ((Fin15AnchoredAtom3073 chi ∧
      ¬Fin15AnchoredAtom0890 chi) ∨
      (Fin15AnchoredAtom3073 chi ∧
      ¬Fin15AnchoredAtom0972 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3073 chi ∧
      ¬Fin15AnchoredAtom1357 chi) ∨
      ((¬Fin15AnchoredAtom3073 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0892 chi ∧
      Fin15AnchoredAtom0927 chi ∧
      Fin15AnchoredAtom0972 chi ∧
      Fin15AnchoredAtom1357 chi) ∨
      (Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom0890 chi))) ∨
      (((Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom0893 chi) ∨
      (Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom0928 chi)) ∨
      ((Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom0973 chi) ∨
      (Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom1358 chi)))) ∨
      ((((¬Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1358 chi) ∨
      (Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom0890 chi)) ∨
      ((Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom0894 chi) ∨
      (Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom0929 chi))) ∨
      (((Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom0974 chi) ∨
      (Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom1359 chi)) ∨
      ((¬Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1359 chi) ∨
      (Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom0890 chi))))) ∨
      (((((Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom0895 chi) ∨
      (Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom0930 chi)) ∨
      ((Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom1360 chi))) ∨
      (((¬Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1360 chi) ∨
      (Fin15AnchoredAtom3077 chi ∧
      ¬Fin15AnchoredAtom0891 chi)) ∨
      ((Fin15AnchoredAtom3077 chi ∧
      ¬Fin15AnchoredAtom0892 chi) ∨
      (Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom0891 chi)))) ∨
      ((((Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom0893 chi) ∨
      (Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom0932 chi)) ∨
      ((Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom0977 chi) ∨
      (Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom1362 chi))) ∨
      (((¬Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1362 chi) ∨
      (Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom0891 chi)) ∨
      ((Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom0894 chi) ∨
      (Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom0933 chi)))))) ∨
      ((((((Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom0978 chi) ∨
      (Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom1363 chi)) ∨
      ((¬Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1363 chi) ∨
      (Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom0891 chi))) ∨
      (((Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom0895 chi) ∨
      (Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom0934 chi)) ∨
      ((Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom0979 chi) ∨
      (Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom1364 chi)))) ∨
      ((((¬Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1364 chi) ∨
      (Fin15AnchoredAtom3081 chi ∧
      ¬Fin15AnchoredAtom0893 chi)) ∨
      ((Fin15AnchoredAtom3081 chi ∧
      ¬Fin15AnchoredAtom1365 chi) ∨
      (¬Fin15AnchoredAtom3081 chi ∧
      Fin15AnchoredAtom0892 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0935 chi ∧
      Fin15AnchoredAtom0980 chi ∧
      Fin15AnchoredAtom1365 chi))) ∨
      (((Fin15AnchoredAtom3082 chi ∧
      ¬Fin15AnchoredAtom0936 chi) ∨
      (Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom0893 chi)) ∨
      ((Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom0894 chi) ∨
      (Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom0938 chi))))) ∨
      (((((Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom0983 chi) ∨
      (Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom1368 chi)) ∨
      ((¬Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1368 chi) ∨
      (Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom0893 chi))) ∨
      (((Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom0895 chi) ∨
      (Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom0939 chi)) ∨
      ((Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom0984 chi) ∨
      (Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom1369 chi)))) ∨
      ((((¬Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1369 chi) ∨
      (Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom0894 chi)) ∨
      ((Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom0895 chi) ∨
      (Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom0940 chi))) ∨
      (((Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom0985 chi) ∨
      (Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom1370 chi)) ∨
      ((¬Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1370 chi) ∨
      (Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom0896 chi))))))) ∨
      ((((((Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom0897 chi) ∨
      ((Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom0905 chi) ∨
      (Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom0986 chi))) ∨
      (((Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom1371 chi) ∨
      (¬Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom1371 chi)) ∨
      ((Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom0898 chi)))) ∨
      ((((Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom0906 chi) ∨
      (Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom0987 chi)) ∨
      ((Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom1372 chi) ∨
      (¬Fin15AnchoredAtom3088 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom1372 chi))) ∨
      (((Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom0899 chi)) ∨
      ((Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom0907 chi) ∨
      (Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom0988 chi))))) ∨
      (((((Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom1373 chi) ∨
      (¬Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom1373 chi)) ∨
      ((Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom0900 chi))) ∨
      (((Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom0908 chi) ∨
      (Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom0989 chi)) ∨
      ((Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom1374 chi) ∨
      (¬Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom1374 chi)))) ∨
      ((((Fin15AnchoredAtom3091 chi ∧
      ¬Fin15AnchoredAtom1375 chi) ∨
      (¬Fin15AnchoredAtom3091 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0901 chi ∧
      Fin15AnchoredAtom0909 chi ∧
      Fin15AnchoredAtom0990 chi ∧
      Fin15AnchoredAtom1375 chi)) ∨
      ((Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom0902 chi))) ∨
      (((Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom0910 chi) ∨
      (Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom0991 chi)) ∨
      ((Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom1376 chi) ∨
      (¬Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1376 chi)))))) ∨
      ((((((Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom0903 chi)) ∨
      ((Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom0911 chi) ∨
      (Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom0992 chi))) ∨
      (((Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom1377 chi) ∨
      (¬Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1377 chi)) ∨
      ((Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom0896 chi) ∨
      (Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom0904 chi)))) ∨
      ((((Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom0912 chi) ∨
      (Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom0993 chi)) ∨
      ((Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom1378 chi) ∨
      (¬Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1378 chi))) ∨
      (((Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom0897 chi) ∨
      (Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom0898 chi)) ∨
      ((Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom0913 chi) ∨
      (Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom1379 chi))))) ∨
      (((((¬Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom1379 chi) ∨
      (Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom0897 chi)) ∨
      ((Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom0899 chi) ∨
      (Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom0914 chi))) ∨
      (((Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom0995 chi) ∨
      (Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom1380 chi)) ∨
      ((¬Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1380 chi) ∨
      (Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom0897 chi)))) ∨
      ((((Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom0900 chi) ∨
      (Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom0915 chi)) ∨
      ((Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom0996 chi) ∨
      (Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom1381 chi))) ∨
      (((¬Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1381 chi) ∨
      (Fin15AnchoredAtom3098 chi ∧
      ¬Fin15AnchoredAtom0897 chi)) ∨
      ((Fin15AnchoredAtom3098 chi ∧
      ¬Fin15AnchoredAtom1382 chi) ∨
      (Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom0897 chi)))))))))) := by
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
                exact fin15Anchored_clause21201 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21202 chi hbad
                ·
                  exact fin15Anchored_clause21203 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21204 chi hbad
                ·
                  exact fin15Anchored_clause21205 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21206 chi hbad
                ·
                  exact fin15Anchored_clause21207 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21208 chi hbad
                ·
                  exact fin15Anchored_clause21209 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21210 chi hbad
                ·
                  exact fin15Anchored_clause21211 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21212 chi hbad
                ·
                  exact fin15Anchored_clause21213 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21214 chi hbad
                ·
                  exact fin15Anchored_clause21215 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21216 chi hbad
                ·
                  exact fin15Anchored_clause21217 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21218 chi hbad
                ·
                  exact fin15Anchored_clause21219 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21220 chi hbad
                ·
                  exact fin15Anchored_clause21221 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21222 chi hbad
                ·
                  exact fin15Anchored_clause21223 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21224 chi hbad
                ·
                  exact fin15Anchored_clause21225 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21226 chi hbad
                ·
                  exact fin15Anchored_clause21227 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21228 chi hbad
                ·
                  exact fin15Anchored_clause21229 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21230 chi hbad
                ·
                  exact fin15Anchored_clause21231 chi hbad
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
                  exact fin15Anchored_clause21232 chi hbad
                ·
                  exact fin15Anchored_clause21233 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21234 chi hbad
                ·
                  exact fin15Anchored_clause21235 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21236 chi hbad
                ·
                  exact fin15Anchored_clause21237 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21238 chi hbad
                ·
                  exact fin15Anchored_clause21239 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21240 chi hbad
                ·
                  exact fin15Anchored_clause21241 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21242 chi hbad
                ·
                  exact fin15Anchored_clause21243 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21244 chi hbad
                ·
                  exact fin15Anchored_clause21245 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21246 chi hbad
                ·
                  exact fin15Anchored_clause21247 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21248 chi hbad
                ·
                  exact fin15Anchored_clause21249 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21250 chi hbad
                ·
                  exact fin15Anchored_clause21251 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21252 chi hbad
                ·
                  exact fin15Anchored_clause21253 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21254 chi hbad
                ·
                  exact fin15Anchored_clause21255 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21256 chi hbad
                ·
                  exact fin15Anchored_clause21257 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21258 chi hbad
                ·
                  exact fin15Anchored_clause21259 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21260 chi hbad
                ·
                  exact fin15Anchored_clause21261 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21262 chi hbad
                ·
                  exact fin15Anchored_clause21263 chi hbad
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
                exact fin15Anchored_clause21264 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21265 chi hbad
                ·
                  exact fin15Anchored_clause21266 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21267 chi hbad
                ·
                  exact fin15Anchored_clause21268 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21269 chi hbad
                ·
                  exact fin15Anchored_clause21270 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21271 chi hbad
                ·
                  exact fin15Anchored_clause21272 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21273 chi hbad
                ·
                  exact fin15Anchored_clause21274 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21275 chi hbad
                ·
                  exact fin15Anchored_clause21276 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21277 chi hbad
                ·
                  exact fin15Anchored_clause21278 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21279 chi hbad
                ·
                  exact fin15Anchored_clause21280 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21281 chi hbad
                ·
                  exact fin15Anchored_clause21282 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21283 chi hbad
                ·
                  exact fin15Anchored_clause21284 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21285 chi hbad
                ·
                  exact fin15Anchored_clause21286 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21287 chi hbad
                ·
                  exact fin15Anchored_clause21288 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21289 chi hbad
                ·
                  exact fin15Anchored_clause21290 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21291 chi hbad
                ·
                  exact fin15Anchored_clause21292 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21293 chi hbad
                ·
                  exact fin15Anchored_clause21294 chi hbad
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
                  exact fin15Anchored_clause21295 chi hbad
                ·
                  exact fin15Anchored_clause21296 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21297 chi hbad
                ·
                  exact fin15Anchored_clause21298 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21299 chi hbad
                ·
                  exact fin15Anchored_clause21300 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21301 chi hbad
                ·
                  exact fin15Anchored_clause21302 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21303 chi hbad
                ·
                  exact fin15Anchored_clause21304 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21305 chi hbad
                ·
                  exact fin15Anchored_clause21306 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21307 chi hbad
                ·
                  exact fin15Anchored_clause21308 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21309 chi hbad
                ·
                  exact fin15Anchored_clause21310 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21311 chi hbad
                ·
                  exact fin15Anchored_clause21312 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21313 chi hbad
                ·
                  exact fin15Anchored_clause21314 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21315 chi hbad
                ·
                  exact fin15Anchored_clause21316 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21317 chi hbad
                ·
                  exact fin15Anchored_clause21318 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21319 chi hbad
                ·
                  exact fin15Anchored_clause21320 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21321 chi hbad
                ·
                  exact fin15Anchored_clause21322 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21323 chi hbad
                ·
                  exact fin15Anchored_clause21324 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21325 chi hbad
                ·
                  exact fin15Anchored_clause21326 chi hbad
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
                exact fin15Anchored_clause21327 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21328 chi hbad
                ·
                  exact fin15Anchored_clause21329 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21330 chi hbad
                ·
                  exact fin15Anchored_clause21331 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21332 chi hbad
                ·
                  exact fin15Anchored_clause21333 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21334 chi hbad
                ·
                  exact fin15Anchored_clause21335 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21336 chi hbad
                ·
                  exact fin15Anchored_clause21337 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21338 chi hbad
                ·
                  exact fin15Anchored_clause21339 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21340 chi hbad
                ·
                  exact fin15Anchored_clause21341 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21342 chi hbad
                ·
                  exact fin15Anchored_clause21343 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21344 chi hbad
                ·
                  exact fin15Anchored_clause21345 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21346 chi hbad
                ·
                  exact fin15Anchored_clause21347 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21348 chi hbad
                ·
                  exact fin15Anchored_clause21349 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21350 chi hbad
                ·
                  exact fin15Anchored_clause21351 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21352 chi hbad
                ·
                  exact fin15Anchored_clause21353 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21354 chi hbad
                ·
                  exact fin15Anchored_clause21355 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21356 chi hbad
                ·
                  exact fin15Anchored_clause21357 chi hbad
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
                  exact fin15Anchored_clause21358 chi hbad
                ·
                  exact fin15Anchored_clause21359 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21360 chi hbad
                ·
                  exact fin15Anchored_clause21361 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21362 chi hbad
                ·
                  exact fin15Anchored_clause21363 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21364 chi hbad
                ·
                  exact fin15Anchored_clause21365 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21366 chi hbad
                ·
                  exact fin15Anchored_clause21367 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21368 chi hbad
                ·
                  exact fin15Anchored_clause21369 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21370 chi hbad
                ·
                  exact fin15Anchored_clause21371 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21372 chi hbad
                ·
                  exact fin15Anchored_clause21373 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21374 chi hbad
                ·
                  exact fin15Anchored_clause21375 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21376 chi hbad
                ·
                  exact fin15Anchored_clause21377 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21378 chi hbad
                ·
                  exact fin15Anchored_clause21379 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21380 chi hbad
                ·
                  exact fin15Anchored_clause21381 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21382 chi hbad
                ·
                  exact fin15Anchored_clause21383 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21384 chi hbad
                ·
                  exact fin15Anchored_clause21385 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21386 chi hbad
                ·
                  exact fin15Anchored_clause21387 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21388 chi hbad
                ·
                  exact fin15Anchored_clause21389 chi hbad
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
                exact fin15Anchored_clause21390 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21391 chi hbad
                ·
                  exact fin15Anchored_clause21392 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21393 chi hbad
                ·
                  exact fin15Anchored_clause21394 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21395 chi hbad
                ·
                  exact fin15Anchored_clause21396 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21397 chi hbad
                ·
                  exact fin15Anchored_clause21398 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21399 chi hbad
                ·
                  exact fin15Anchored_clause21400 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21401 chi hbad
                ·
                  exact fin15Anchored_clause21402 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21403 chi hbad
                ·
                  exact fin15Anchored_clause21404 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21405 chi hbad
                ·
                  exact fin15Anchored_clause21406 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21407 chi hbad
                ·
                  exact fin15Anchored_clause21408 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21409 chi hbad
                ·
                  exact fin15Anchored_clause21410 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21411 chi hbad
                ·
                  exact fin15Anchored_clause21412 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21413 chi hbad
                ·
                  exact fin15Anchored_clause21414 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21415 chi hbad
                ·
                  exact fin15Anchored_clause21416 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21417 chi hbad
                ·
                  exact fin15Anchored_clause21418 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21419 chi hbad
                ·
                  exact fin15Anchored_clause21420 chi hbad
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
                  exact fin15Anchored_clause21421 chi hbad
                ·
                  exact fin15Anchored_clause21422 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21423 chi hbad
                ·
                  exact fin15Anchored_clause21424 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21425 chi hbad
                ·
                  exact fin15Anchored_clause21426 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21427 chi hbad
                ·
                  exact fin15Anchored_clause21428 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21429 chi hbad
                ·
                  exact fin15Anchored_clause21430 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21431 chi hbad
                ·
                  exact fin15Anchored_clause21432 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21433 chi hbad
                ·
                  exact fin15Anchored_clause21434 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21435 chi hbad
                ·
                  exact fin15Anchored_clause21436 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21437 chi hbad
                ·
                  exact fin15Anchored_clause21438 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21439 chi hbad
                ·
                  exact fin15Anchored_clause21440 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21441 chi hbad
                ·
                  exact fin15Anchored_clause21442 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21443 chi hbad
                ·
                  exact fin15Anchored_clause21444 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21445 chi hbad
                ·
                  exact fin15Anchored_clause21446 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21447 chi hbad
                ·
                  exact fin15Anchored_clause21448 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21449 chi hbad
                ·
                  exact fin15Anchored_clause21450 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21451 chi hbad
                ·
                  exact fin15Anchored_clause21452 chi hbad

end ErdosSzekeres

end
