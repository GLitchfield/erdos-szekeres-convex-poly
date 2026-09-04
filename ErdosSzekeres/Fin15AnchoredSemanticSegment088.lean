module

public import ErdosSzekeres.Fin15AnchoredClauseChunk173
public import ErdosSzekeres.Fin15AnchoredClauseChunk174
public import ErdosSzekeres.Fin15AnchoredClauseChunk175

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 088. -/

theorem fin15Anchored_rejectSemanticSegment088
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom0957 chi) ∨
      ((Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom0979 chi) ∨
      (Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom1043 chi))) ∨
      (((Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom1548 chi) ∨
      (¬Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1548 chi)) ∨
      ((Fin15AnchoredAtom3265 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (Fin15AnchoredAtom3266 chi ∧
      ¬Fin15AnchoredAtom0956 chi)))) ∨
      ((((Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom0956 chi)) ∨
      ((Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom0983 chi) ∨
      (Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom1047 chi))) ∨
      (((Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom1552 chi) ∨
      (¬Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1552 chi)) ∨
      ((Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom0957 chi))))) ∨
      (((((Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom0984 chi) ∨
      (Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom1048 chi)) ∨
      ((Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom1553 chi) ∨
      (¬Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1553 chi))) ∨
      (((Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom0956 chi) ∨
      (Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom0957 chi)) ∨
      ((Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom0985 chi) ∨
      (Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom1049 chi)))) ∨
      ((((Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom1554 chi) ∨
      (¬Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1554 chi)) ∨
      ((Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom0958 chi) ∨
      (Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom0959 chi))) ∨
      (((Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom0965 chi) ∨
      (Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom1050 chi)) ∨
      ((Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom1555 chi) ∨
      (¬Fin15AnchoredAtom3271 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1555 chi)))))) ∨
      ((((((Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom0958 chi) ∨
      (Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom0960 chi)) ∨
      ((Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom0966 chi) ∨
      (Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom1051 chi))) ∨
      (((Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom1556 chi) ∨
      (¬Fin15AnchoredAtom3272 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1556 chi)) ∨
      ((Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom0958 chi) ∨
      (Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom0962 chi)))) ∨
      ((((Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom0968 chi) ∨
      (Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom1053 chi)) ∨
      ((Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom1558 chi) ∨
      (¬Fin15AnchoredAtom3274 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1558 chi))) ∨
      (((Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom0958 chi) ∨
      (Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom0963 chi)) ∨
      ((Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom0969 chi) ∨
      (Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom1054 chi))))) ∨
      (((((Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom1559 chi) ∨
      (¬Fin15AnchoredAtom3275 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1559 chi)) ∨
      ((Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom0964 chi) ∨
      (Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom0970 chi))) ∨
      (((Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom1055 chi) ∨
      (Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom1560 chi)) ∨
      ((¬Fin15AnchoredAtom3276 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1560 chi) ∨
      (Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom0959 chi)))) ∨
      ((((Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom0960 chi) ∨
      (Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom0971 chi)) ∨
      ((Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom1056 chi) ∨
      (Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom1561 chi))) ∨
      (((¬Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1561 chi) ∨
      (Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom0959 chi)) ∨
      ((Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom0972 chi) ∨
      (Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom1057 chi))))))) ∨
      ((((((Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom1562 chi) ∨
      ((Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom0959 chi) ∨
      (Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom0962 chi))) ∨
      (((Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom0973 chi) ∨
      (Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom1058 chi)) ∨
      ((Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom1563 chi) ∨
      (¬Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1563 chi)))) ∨
      ((((Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom0959 chi) ∨
      (Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom0963 chi)) ∨
      ((Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom0974 chi) ∨
      (Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom1059 chi))) ∨
      (((Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom1564 chi) ∨
      (¬Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1564 chi)) ∨
      ((Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom0959 chi) ∨
      (Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom0964 chi))))) ∨
      (((((Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom1060 chi)) ∨
      ((Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom1565 chi) ∨
      (¬Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1565 chi))) ∨
      (((Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom0960 chi) ∨
      (Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom0961 chi)) ∨
      ((Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom1061 chi) ∨
      (Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom0960 chi)))) ∨
      ((((Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom0962 chi) ∨
      (Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom0977 chi)) ∨
      ((Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom1062 chi) ∨
      (Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom1567 chi))) ∨
      (((¬Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1567 chi) ∨
      (Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom0960 chi)) ∨
      ((Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom0963 chi) ∨
      (Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom0978 chi)))))) ∨
      ((((((Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom1063 chi) ∨
      (Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom1568 chi)) ∨
      ((¬Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1568 chi) ∨
      (Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom0960 chi))) ∨
      (((Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom0964 chi) ∨
      (Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom0979 chi)) ∨
      ((Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom1064 chi) ∨
      (Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom1569 chi)))) ∨
      ((((¬Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1569 chi) ∨
      (Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom0962 chi)) ∨
      ((Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom0980 chi) ∨
      (Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom1065 chi))) ∨
      (((¬Fin15AnchoredAtom3286 chi ∧
      Fin15AnchoredAtom0961 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0980 chi ∧
      Fin15AnchoredAtom1065 chi ∧
      Fin15AnchoredAtom1570 chi) ∨
      (Fin15AnchoredAtom3287 chi ∧
      ¬Fin15AnchoredAtom0963 chi)) ∨
      ((Fin15AnchoredAtom3287 chi ∧
      ¬Fin15AnchoredAtom0981 chi) ∨
      (Fin15AnchoredAtom3288 chi ∧
      ¬Fin15AnchoredAtom0964 chi))))) ∨
      (((((Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom0962 chi) ∨
      (Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom0963 chi)) ∨
      ((Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom0983 chi) ∨
      (Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom1068 chi))) ∨
      (((Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom1573 chi) ∨
      (¬Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1573 chi)) ∨
      ((Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom0962 chi) ∨
      (Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom0964 chi)))) ∨
      ((((Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom0984 chi) ∨
      (Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom1069 chi)) ∨
      ((Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom1574 chi) ∨
      (¬Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1574 chi))) ∨
      (((Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom0963 chi) ∨
      (Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom0964 chi)) ∨
      ((Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom0985 chi) ∨
      (Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom1070 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom1575 chi) ∨
      ((¬Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1575 chi) ∨
      (Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom0965 chi))) ∨
      (((Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom0966 chi) ∨
      (Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom0971 chi)) ∨
      ((Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom1071 chi) ∨
      (Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom1576 chi)))) ∨
      ((((¬Fin15AnchoredAtom3292 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1576 chi) ∨
      (Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom0965 chi)) ∨
      ((Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom0968 chi) ∨
      (Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom0973 chi))) ∨
      (((Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom1073 chi) ∨
      (Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom1578 chi)) ∨
      ((¬Fin15AnchoredAtom3294 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1578 chi) ∨
      (Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom0965 chi))))) ∨
      (((((Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom0969 chi) ∨
      (Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom0974 chi)) ∨
      ((Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom1074 chi) ∨
      (Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom1579 chi))) ∨
      (((¬Fin15AnchoredAtom3295 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1579 chi) ∨
      (Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom0965 chi)) ∨
      ((Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom1075 chi)))) ∨
      ((((Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom1580 chi) ∨
      (¬Fin15AnchoredAtom3296 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1075 chi ∧
      Fin15AnchoredAtom1580 chi)) ∨
      ((Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom0966 chi) ∨
      (Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom0968 chi))) ∨
      (((Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom0977 chi) ∨
      (Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom1077 chi)) ∨
      ((Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom1582 chi) ∨
      (¬Fin15AnchoredAtom3298 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1582 chi)))))) ∨
      ((((((Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom0966 chi) ∨
      (Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom0969 chi)) ∨
      ((Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom0978 chi) ∨
      (Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom1078 chi))) ∨
      (((Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom1583 chi) ∨
      (¬Fin15AnchoredAtom3299 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1583 chi)) ∨
      ((Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom0966 chi) ∨
      (Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom0970 chi)))) ∨
      ((((Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom0979 chi) ∨
      (Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom1079 chi)) ∨
      ((Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom1584 chi) ∨
      (¬Fin15AnchoredAtom3300 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1079 chi ∧
      Fin15AnchoredAtom1584 chi))) ∨
      (((Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom0968 chi) ∨
      (Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom0969 chi)) ∨
      ((Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom0983 chi) ∨
      (Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom1083 chi))))) ∨
      (((((Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom1588 chi) ∨
      (¬Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1588 chi)) ∨
      ((Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom0968 chi) ∨
      (Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom0984 chi))) ∨
      (((Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom1084 chi) ∨
      (Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom1589 chi)) ∨
      ((¬Fin15AnchoredAtom3305 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1589 chi) ∨
      (Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom0969 chi)))) ∨
      ((((Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom0970 chi) ∨
      (Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom0985 chi)) ∨
      ((Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom1085 chi) ∨
      (Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom1590 chi))) ∨
      (((¬Fin15AnchoredAtom3306 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1590 chi) ∨
      (Fin15AnchoredAtom3307 chi ∧
      ¬Fin15AnchoredAtom1591 chi)) ∨
      ((Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom0971 chi) ∨
      (Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom0973 chi))))))) ∨
      ((((((Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom0977 chi) ∨
      ((Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom1087 chi) ∨
      (Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom1592 chi))) ∨
      (((¬Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1592 chi) ∨
      (Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom0971 chi)) ∨
      ((Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom0974 chi) ∨
      (Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom0978 chi)))) ∨
      ((((Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom1088 chi) ∨
      (Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom1593 chi)) ∨
      ((¬Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1593 chi) ∨
      (Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom0971 chi))) ∨
      (((Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom0979 chi)) ∨
      ((Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom1089 chi) ∨
      (Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom1594 chi))))) ∨
      (((((¬Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1594 chi) ∨
      (Fin15AnchoredAtom3311 chi ∧
      ¬Fin15AnchoredAtom0973 chi)) ∨
      ((Fin15AnchoredAtom3311 chi ∧
      ¬Fin15AnchoredAtom0980 chi) ∨
      (Fin15AnchoredAtom3311 chi ∧
      ¬Fin15AnchoredAtom1595 chi))) ∨
      (((¬Fin15AnchoredAtom3311 chi ∧
      Fin15AnchoredAtom0972 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom0980 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1595 chi) ∨
      (Fin15AnchoredAtom3312 chi ∧
      ¬Fin15AnchoredAtom0974 chi)) ∨
      ((Fin15AnchoredAtom3312 chi ∧
      ¬Fin15AnchoredAtom0981 chi) ∨
      (Fin15AnchoredAtom3312 chi ∧
      ¬Fin15AnchoredAtom1596 chi)))) ∨
      ((((Fin15AnchoredAtom3313 chi ∧
      ¬Fin15AnchoredAtom0982 chi) ∨
      (Fin15AnchoredAtom3313 chi ∧
      ¬Fin15AnchoredAtom1092 chi)) ∨
      ((Fin15AnchoredAtom3313 chi ∧
      ¬Fin15AnchoredAtom1597 chi) ∨
      (Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom0973 chi))) ∨
      (((Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom0974 chi) ∨
      (Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom0983 chi)) ∨
      ((Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom1093 chi) ∨
      (Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom1598 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1598 chi) ∨
      (Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom0973 chi)) ∨
      ((Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom0984 chi))) ∨
      (((Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom1094 chi) ∨
      (Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom1599 chi)) ∨
      ((¬Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1599 chi) ∨
      (Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom0974 chi)))) ∨
      ((((Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom0985 chi)) ∨
      ((Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom1095 chi) ∨
      (Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom1600 chi))) ∨
      (((¬Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1600 chi) ∨
      (Fin15AnchoredAtom3317 chi ∧
      ¬Fin15AnchoredAtom0977 chi)) ∨
      ((Fin15AnchoredAtom3317 chi ∧
      ¬Fin15AnchoredAtom0980 chi) ∨
      (Fin15AnchoredAtom3317 chi ∧
      ¬Fin15AnchoredAtom1096 chi))))) ∨
      (((((Fin15AnchoredAtom3318 chi ∧
      ¬Fin15AnchoredAtom0981 chi) ∨
      (Fin15AnchoredAtom3318 chi ∧
      ¬Fin15AnchoredAtom1097 chi)) ∨
      ((Fin15AnchoredAtom3318 chi ∧
      ¬Fin15AnchoredAtom1602 chi) ∨
      (Fin15AnchoredAtom3319 chi ∧
      ¬Fin15AnchoredAtom1098 chi))) ∨
      (((Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom0977 chi) ∨
      (Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom0978 chi)) ∨
      ((Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom0983 chi) ∨
      (Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom1099 chi)))) ∨
      ((((Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom1604 chi) ∨
      (¬Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1604 chi)) ∨
      ((Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom0977 chi) ∨
      (Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom0979 chi))) ∨
      (((Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom0984 chi) ∨
      (Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom1100 chi)) ∨
      ((Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom1605 chi) ∨
      (¬Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1605 chi)))))))))) := by
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
                exact fin15Anchored_clause22211 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22212 chi hbad
                ·
                  exact fin15Anchored_clause22213 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22214 chi hbad
                ·
                  exact fin15Anchored_clause22215 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22216 chi hbad
                ·
                  exact fin15Anchored_clause22217 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22218 chi hbad
                ·
                  exact fin15Anchored_clause22219 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22220 chi hbad
                ·
                  exact fin15Anchored_clause22221 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22222 chi hbad
                ·
                  exact fin15Anchored_clause22223 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22224 chi hbad
                ·
                  exact fin15Anchored_clause22225 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22226 chi hbad
                ·
                  exact fin15Anchored_clause22227 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22228 chi hbad
                ·
                  exact fin15Anchored_clause22229 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22230 chi hbad
                ·
                  exact fin15Anchored_clause22231 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22232 chi hbad
                ·
                  exact fin15Anchored_clause22233 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22234 chi hbad
                ·
                  exact fin15Anchored_clause22235 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22236 chi hbad
                ·
                  exact fin15Anchored_clause22237 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22238 chi hbad
                ·
                  exact fin15Anchored_clause22239 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22240 chi hbad
                ·
                  exact fin15Anchored_clause22241 chi hbad
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
                  exact fin15Anchored_clause22242 chi hbad
                ·
                  exact fin15Anchored_clause22243 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22244 chi hbad
                ·
                  exact fin15Anchored_clause22245 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22246 chi hbad
                ·
                  exact fin15Anchored_clause22247 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22248 chi hbad
                ·
                  exact fin15Anchored_clause22249 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22250 chi hbad
                ·
                  exact fin15Anchored_clause22251 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22252 chi hbad
                ·
                  exact fin15Anchored_clause22253 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22254 chi hbad
                ·
                  exact fin15Anchored_clause22255 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22256 chi hbad
                ·
                  exact fin15Anchored_clause22257 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22258 chi hbad
                ·
                  exact fin15Anchored_clause22259 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22260 chi hbad
                ·
                  exact fin15Anchored_clause22261 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22262 chi hbad
                ·
                  exact fin15Anchored_clause22263 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22264 chi hbad
                ·
                  exact fin15Anchored_clause22265 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22266 chi hbad
                ·
                  exact fin15Anchored_clause22267 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22268 chi hbad
                ·
                  exact fin15Anchored_clause22269 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22270 chi hbad
                ·
                  exact fin15Anchored_clause22271 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22272 chi hbad
                ·
                  exact fin15Anchored_clause22273 chi hbad
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
                exact fin15Anchored_clause22274 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22275 chi hbad
                ·
                  exact fin15Anchored_clause22276 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22277 chi hbad
                ·
                  exact fin15Anchored_clause22278 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22279 chi hbad
                ·
                  exact fin15Anchored_clause22280 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22281 chi hbad
                ·
                  exact fin15Anchored_clause22282 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22283 chi hbad
                ·
                  exact fin15Anchored_clause22284 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22285 chi hbad
                ·
                  exact fin15Anchored_clause22286 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22287 chi hbad
                ·
                  exact fin15Anchored_clause22288 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22289 chi hbad
                ·
                  exact fin15Anchored_clause22290 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22291 chi hbad
                ·
                  exact fin15Anchored_clause22292 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22293 chi hbad
                ·
                  exact fin15Anchored_clause22294 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22295 chi hbad
                ·
                  exact fin15Anchored_clause22296 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22297 chi hbad
                ·
                  exact fin15Anchored_clause22298 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22299 chi hbad
                ·
                  exact fin15Anchored_clause22300 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22301 chi hbad
                ·
                  exact fin15Anchored_clause22302 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22303 chi hbad
                ·
                  exact fin15Anchored_clause22304 chi hbad
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
                  exact fin15Anchored_clause22305 chi hbad
                ·
                  exact fin15Anchored_clause22306 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22307 chi hbad
                ·
                  exact fin15Anchored_clause22308 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22309 chi hbad
                ·
                  exact fin15Anchored_clause22310 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22311 chi hbad
                ·
                  exact fin15Anchored_clause22312 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22313 chi hbad
                ·
                  exact fin15Anchored_clause22314 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22315 chi hbad
                ·
                  exact fin15Anchored_clause22316 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22317 chi hbad
                ·
                  exact fin15Anchored_clause22318 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22319 chi hbad
                ·
                  exact fin15Anchored_clause22320 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22321 chi hbad
                ·
                  exact fin15Anchored_clause22322 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22323 chi hbad
                ·
                  exact fin15Anchored_clause22324 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22325 chi hbad
                ·
                  exact fin15Anchored_clause22326 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22327 chi hbad
                ·
                  exact fin15Anchored_clause22328 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22329 chi hbad
                ·
                  exact fin15Anchored_clause22330 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22331 chi hbad
                ·
                  exact fin15Anchored_clause22332 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22333 chi hbad
                ·
                  exact fin15Anchored_clause22334 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22335 chi hbad
                ·
                  exact fin15Anchored_clause22336 chi hbad
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
                exact fin15Anchored_clause22337 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22338 chi hbad
                ·
                  exact fin15Anchored_clause22339 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22340 chi hbad
                ·
                  exact fin15Anchored_clause22341 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22342 chi hbad
                ·
                  exact fin15Anchored_clause22343 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22344 chi hbad
                ·
                  exact fin15Anchored_clause22345 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22346 chi hbad
                ·
                  exact fin15Anchored_clause22347 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22348 chi hbad
                ·
                  exact fin15Anchored_clause22349 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22350 chi hbad
                ·
                  exact fin15Anchored_clause22351 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22352 chi hbad
                ·
                  exact fin15Anchored_clause22353 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22354 chi hbad
                ·
                  exact fin15Anchored_clause22355 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22356 chi hbad
                ·
                  exact fin15Anchored_clause22357 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22358 chi hbad
                ·
                  exact fin15Anchored_clause22359 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22360 chi hbad
                ·
                  exact fin15Anchored_clause22361 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22362 chi hbad
                ·
                  exact fin15Anchored_clause22363 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22364 chi hbad
                ·
                  exact fin15Anchored_clause22365 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22366 chi hbad
                ·
                  exact fin15Anchored_clause22367 chi hbad
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
                  exact fin15Anchored_clause22368 chi hbad
                ·
                  exact fin15Anchored_clause22369 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22370 chi hbad
                ·
                  exact fin15Anchored_clause22371 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22372 chi hbad
                ·
                  exact fin15Anchored_clause22373 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22374 chi hbad
                ·
                  exact fin15Anchored_clause22375 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22376 chi hbad
                ·
                  exact fin15Anchored_clause22377 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22378 chi hbad
                ·
                  exact fin15Anchored_clause22379 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22380 chi hbad
                ·
                  exact fin15Anchored_clause22381 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22382 chi hbad
                ·
                  exact fin15Anchored_clause22383 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22384 chi hbad
                ·
                  exact fin15Anchored_clause22385 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22386 chi hbad
                ·
                  exact fin15Anchored_clause22387 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22388 chi hbad
                ·
                  exact fin15Anchored_clause22389 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22390 chi hbad
                ·
                  exact fin15Anchored_clause22391 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22392 chi hbad
                ·
                  exact fin15Anchored_clause22393 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22394 chi hbad
                ·
                  exact fin15Anchored_clause22395 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22396 chi hbad
                ·
                  exact fin15Anchored_clause22397 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22398 chi hbad
                ·
                  exact fin15Anchored_clause22399 chi hbad
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
                exact fin15Anchored_clause22400 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22401 chi hbad
                ·
                  exact fin15Anchored_clause22402 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22403 chi hbad
                ·
                  exact fin15Anchored_clause22404 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22405 chi hbad
                ·
                  exact fin15Anchored_clause22406 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22407 chi hbad
                ·
                  exact fin15Anchored_clause22408 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22409 chi hbad
                ·
                  exact fin15Anchored_clause22410 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22411 chi hbad
                ·
                  exact fin15Anchored_clause22412 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22413 chi hbad
                ·
                  exact fin15Anchored_clause22414 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22415 chi hbad
                ·
                  exact fin15Anchored_clause22416 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22417 chi hbad
                ·
                  exact fin15Anchored_clause22418 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22419 chi hbad
                ·
                  exact fin15Anchored_clause22420 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22421 chi hbad
                ·
                  exact fin15Anchored_clause22422 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22423 chi hbad
                ·
                  exact fin15Anchored_clause22424 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22425 chi hbad
                ·
                  exact fin15Anchored_clause22426 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22427 chi hbad
                ·
                  exact fin15Anchored_clause22428 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22429 chi hbad
                ·
                  exact fin15Anchored_clause22430 chi hbad
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
                  exact fin15Anchored_clause22431 chi hbad
                ·
                  exact fin15Anchored_clause22432 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22433 chi hbad
                ·
                  exact fin15Anchored_clause22434 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22435 chi hbad
                ·
                  exact fin15Anchored_clause22436 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22437 chi hbad
                ·
                  exact fin15Anchored_clause22438 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22439 chi hbad
                ·
                  exact fin15Anchored_clause22440 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22441 chi hbad
                ·
                  exact fin15Anchored_clause22442 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22443 chi hbad
                ·
                  exact fin15Anchored_clause22444 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22445 chi hbad
                ·
                  exact fin15Anchored_clause22446 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22447 chi hbad
                ·
                  exact fin15Anchored_clause22448 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22449 chi hbad
                ·
                  exact fin15Anchored_clause22450 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22451 chi hbad
                ·
                  exact fin15Anchored_clause22452 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22453 chi hbad
                ·
                  exact fin15Anchored_clause22454 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22455 chi hbad
                ·
                  exact fin15Anchored_clause22456 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22457 chi hbad
                ·
                  exact fin15Anchored_clause22458 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22459 chi hbad
                ·
                  exact fin15Anchored_clause22460 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22461 chi hbad
                ·
                  exact fin15Anchored_clause22462 chi hbad

end ErdosSzekeres

end
