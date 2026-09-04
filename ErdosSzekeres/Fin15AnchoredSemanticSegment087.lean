module

public import ErdosSzekeres.Fin15AnchoredClauseChunk171
public import ErdosSzekeres.Fin15AnchoredClauseChunk172
public import ErdosSzekeres.Fin15AnchoredClauseChunk173

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 087. -/

theorem fin15Anchored_rejectSemanticSegment087
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom1496 chi) ∨
      ((¬Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1496 chi) ∨
      (Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom0941 chi))) ∨
      (((Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      (Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom0956 chi)) ∨
      ((Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom0992 chi) ∨
      (Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom1497 chi)))) ∨
      ((((¬Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1497 chi) ∨
      (Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom0941 chi)) ∨
      ((Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom0949 chi) ∨
      (Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom0957 chi))) ∨
      (((Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom0993 chi) ∨
      (Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom1498 chi)) ∨
      ((¬Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1498 chi) ∨
      (Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom0942 chi))))) ∨
      (((((Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom0943 chi) ∨
      (Fin15AnchoredAtom3215 chi ∧
      ¬Fin15AnchoredAtom1499 chi)) ∨
      ((¬Fin15AnchoredAtom3215 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom1499 chi) ∨
      (Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom0942 chi))) ∨
      (((Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom0944 chi) ∨
      (Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom0959 chi)) ∨
      ((Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom0995 chi) ∨
      (Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom1500 chi)))) ∨
      ((((¬Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1500 chi) ∨
      (Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom0942 chi)) ∨
      ((Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom0945 chi) ∨
      (Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom0960 chi))) ∨
      (((Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom0996 chi) ∨
      (Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom1501 chi)) ∨
      ((¬Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1501 chi) ∨
      (Fin15AnchoredAtom3218 chi ∧
      ¬Fin15AnchoredAtom0942 chi)))))) ∨
      ((((((Fin15AnchoredAtom3218 chi ∧
      ¬Fin15AnchoredAtom1502 chi) ∨
      (Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom0942 chi)) ∨
      ((Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom0947 chi) ∨
      (Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom0962 chi))) ∨
      (((Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom0998 chi) ∨
      (Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom1503 chi)) ∨
      ((¬Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1503 chi) ∨
      (Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom0942 chi)))) ∨
      ((((Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      (Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom0963 chi)) ∨
      ((Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom0999 chi) ∨
      (Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom1504 chi))) ∨
      (((¬Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1504 chi) ∨
      (Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom0942 chi)) ∨
      ((Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom0949 chi) ∨
      (Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom0964 chi))))) ∨
      (((((Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom1000 chi) ∨
      (Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom1505 chi)) ∨
      ((¬Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1505 chi) ∨
      (Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom0943 chi))) ∨
      (((Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom0944 chi) ∨
      (Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom1001 chi)) ∨
      ((Fin15AnchoredAtom3222 chi ∧
      ¬Fin15AnchoredAtom1506 chi) ∨
      (¬Fin15AnchoredAtom3222 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1506 chi)))) ∨
      ((((Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom0943 chi) ∨
      (Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom0945 chi)) ∨
      ((Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom0966 chi) ∨
      (Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom1002 chi))) ∨
      (((Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom1507 chi) ∨
      (¬Fin15AnchoredAtom3223 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1507 chi)) ∨
      ((Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom0943 chi) ∨
      (Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom0947 chi))))))) ∨
      ((((((Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom1509 chi) ∨
      ((¬Fin15AnchoredAtom3225 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1509 chi) ∨
      (Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom0943 chi))) ∨
      (((Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      (Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom0969 chi)) ∨
      ((Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom1005 chi) ∨
      (Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom1510 chi)))) ∨
      ((((¬Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1510 chi) ∨
      (Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom0943 chi)) ∨
      ((Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom0949 chi) ∨
      (Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom1511 chi))) ∨
      (((¬Fin15AnchoredAtom3227 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom1006 chi ∧
      Fin15AnchoredAtom1511 chi) ∨
      (Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom0944 chi)) ∨
      ((Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom0945 chi) ∨
      (Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom0971 chi))))) ∨
      (((((Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom1007 chi) ∨
      (Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom1512 chi)) ∨
      ((¬Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1512 chi) ∨
      (Fin15AnchoredAtom3229 chi ∧
      ¬Fin15AnchoredAtom0944 chi))) ∨
      (((¬Fin15AnchoredAtom3229 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0946 chi ∧
      Fin15AnchoredAtom0972 chi ∧
      Fin15AnchoredAtom1008 chi ∧
      Fin15AnchoredAtom1513 chi) ∨
      (Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom0944 chi)) ∨
      ((Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom0947 chi) ∨
      (Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom0973 chi)))) ∨
      ((((Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom1009 chi) ∨
      (Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom1514 chi)) ∨
      ((¬Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1514 chi) ∨
      (Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom0944 chi))) ∨
      (((Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      (Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom0974 chi)) ∨
      ((Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom1010 chi) ∨
      (Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom1515 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1515 chi) ∨
      (Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom0944 chi)) ∨
      ((Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom0949 chi) ∨
      (Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom0975 chi))) ∨
      (((Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom1011 chi) ∨
      (Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom1516 chi)) ∨
      ((¬Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1516 chi) ∨
      (Fin15AnchoredAtom3233 chi ∧
      ¬Fin15AnchoredAtom0945 chi)))) ∨
      ((((Fin15AnchoredAtom3233 chi ∧
      ¬Fin15AnchoredAtom0946 chi) ∨
      (Fin15AnchoredAtom3233 chi ∧
      ¬Fin15AnchoredAtom1012 chi)) ∨
      ((Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom0945 chi) ∨
      (Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom0947 chi))) ∨
      (((Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom0977 chi) ∨
      (Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom1013 chi)) ∨
      ((Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom1518 chi) ∨
      (¬Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1518 chi))))) ∨
      (((((Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom0945 chi) ∨
      (Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom0948 chi)) ∨
      ((Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom0978 chi) ∨
      (Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom1014 chi))) ∨
      (((Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom1519 chi) ∨
      (¬Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1519 chi)) ∨
      ((Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom0945 chi) ∨
      (Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom0949 chi)))) ∨
      ((((Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom0979 chi) ∨
      (Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom1015 chi)) ∨
      ((Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom1520 chi) ∨
      (¬Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1520 chi))) ∨
      (((Fin15AnchoredAtom3237 chi ∧
      ¬Fin15AnchoredAtom0947 chi) ∨
      (Fin15AnchoredAtom3238 chi ∧
      ¬Fin15AnchoredAtom0948 chi)) ∨
      ((Fin15AnchoredAtom3239 chi ∧
      ¬Fin15AnchoredAtom0949 chi) ∨
      (Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom0947 chi)))))))) ∨
      (((((((Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      ((Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom0983 chi) ∨
      (Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom1019 chi))) ∨
      (((Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom1524 chi) ∨
      (¬Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1524 chi)) ∨
      ((Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom0947 chi) ∨
      (Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom0949 chi)))) ∨
      ((((Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom0984 chi) ∨
      (Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom1020 chi)) ∨
      ((Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom1525 chi) ∨
      (¬Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1525 chi))) ∨
      (((Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom0948 chi) ∨
      (Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom0949 chi)) ∨
      ((Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom0985 chi) ∨
      (Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom1021 chi))))) ∨
      (((((Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom1526 chi) ∨
      (¬Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1526 chi)) ∨
      ((Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom0950 chi) ∨
      (Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom0951 chi))) ∨
      (((Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom0958 chi) ∨
      (Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom1527 chi)) ∨
      ((¬Fin15AnchoredAtom3243 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1527 chi) ∨
      (Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom0950 chi)))) ∨
      ((((Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom0952 chi) ∨
      (Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom0959 chi)) ∨
      ((Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom1023 chi) ∨
      (Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom1528 chi))) ∨
      (((¬Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1528 chi) ∨
      (Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom0950 chi)) ∨
      ((Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom0953 chi) ∨
      (Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom0960 chi)))))) ∨
      ((((((Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom1024 chi) ∨
      (Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom1529 chi)) ∨
      ((¬Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1529 chi) ∨
      (Fin15AnchoredAtom3246 chi ∧
      ¬Fin15AnchoredAtom0950 chi))) ∨
      (((Fin15AnchoredAtom3246 chi ∧
      ¬Fin15AnchoredAtom1530 chi) ∨
      (Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom0950 chi)) ∨
      ((Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom0962 chi)))) ∨
      ((((Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom1026 chi) ∨
      (Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom1531 chi)) ∨
      ((¬Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1531 chi) ∨
      (Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom0950 chi))) ∨
      (((Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom0956 chi) ∨
      (Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom0963 chi)) ∨
      ((Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom1027 chi) ∨
      (Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom1532 chi))))) ∨
      (((((¬Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1532 chi) ∨
      (Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom0950 chi)) ∨
      ((Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom0957 chi) ∨
      (Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom0964 chi))) ∨
      (((Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom1028 chi) ∨
      (Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom1533 chi)) ∨
      ((¬Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1533 chi) ∨
      (Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom0951 chi)))) ∨
      ((((Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom0952 chi) ∨
      (Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom0965 chi)) ∨
      ((Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom1029 chi) ∨
      (Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom1534 chi))) ∨
      (((¬Fin15AnchoredAtom3250 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1534 chi) ∨
      (Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom0951 chi)) ∨
      ((Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom0953 chi) ∨
      (Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom0966 chi))))))) ∨
      (((((((Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom1030 chi) ∨
      (Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom1535 chi)) ∨
      ((¬Fin15AnchoredAtom3251 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1535 chi) ∨
      (Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom0951 chi))) ∨
      (((Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom1032 chi)) ∨
      ((Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom1537 chi) ∨
      (¬Fin15AnchoredAtom3253 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1537 chi)))) ∨
      ((((Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom0951 chi) ∨
      (Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom0956 chi)) ∨
      ((Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom0969 chi) ∨
      (Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom1033 chi))) ∨
      (((Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom1538 chi) ∨
      (¬Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1538 chi)) ∨
      ((Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom0951 chi) ∨
      (Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom0957 chi))))) ∨
      (((((Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom0970 chi) ∨
      (Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom1034 chi)) ∨
      ((Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom1539 chi) ∨
      (¬Fin15AnchoredAtom3255 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom1034 chi ∧
      Fin15AnchoredAtom1539 chi))) ∨
      (((Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom0952 chi) ∨
      (Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom0953 chi)) ∨
      ((Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom0971 chi) ∨
      (Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom1035 chi)))) ∨
      ((((Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom1540 chi) ∨
      (¬Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1540 chi)) ∨
      ((Fin15AnchoredAtom3257 chi ∧
      ¬Fin15AnchoredAtom0952 chi) ∨
      (Fin15AnchoredAtom3257 chi ∧
      ¬Fin15AnchoredAtom1036 chi))) ∨
      (((Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom0952 chi) ∨
      (Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom0955 chi)) ∨
      ((Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom0973 chi) ∨
      (Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom1037 chi)))))) ∨
      ((((((Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom1542 chi) ∨
      (¬Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1542 chi)) ∨
      ((Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom0952 chi) ∨
      (Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom0956 chi))) ∨
      (((Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom0974 chi) ∨
      (Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom1038 chi)) ∨
      ((Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom1543 chi) ∨
      (¬Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1543 chi)))) ∨
      ((((Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom0952 chi) ∨
      (Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom0957 chi)) ∨
      ((Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom0975 chi) ∨
      (Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom1039 chi))) ∨
      (((Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom1544 chi) ∨
      (¬Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1544 chi)) ∨
      ((Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom0953 chi) ∨
      (Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom0954 chi))))) ∨
      (((((Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom1040 chi) ∨
      (Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom1545 chi)) ∨
      ((¬Fin15AnchoredAtom3261 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0954 chi ∧
      Fin15AnchoredAtom0976 chi ∧
      Fin15AnchoredAtom1040 chi ∧
      Fin15AnchoredAtom1545 chi) ∨
      (Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom0953 chi))) ∨
      (((Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom0955 chi) ∨
      (Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom0977 chi)) ∨
      ((Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom1041 chi) ∨
      (Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom1546 chi)))) ∨
      ((((¬Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1546 chi) ∨
      (Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom0953 chi)) ∨
      ((Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom0956 chi) ∨
      (Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom0978 chi))) ∨
      (((Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom1042 chi) ∨
      (Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom1547 chi)) ∨
      ((¬Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1547 chi) ∨
      (Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom0953 chi)))))))))) := by
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
                exact fin15Anchored_clause21958 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21959 chi hbad
                ·
                  exact fin15Anchored_clause21960 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21961 chi hbad
                ·
                  exact fin15Anchored_clause21962 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21963 chi hbad
                ·
                  exact fin15Anchored_clause21964 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21965 chi hbad
                ·
                  exact fin15Anchored_clause21966 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21967 chi hbad
                ·
                  exact fin15Anchored_clause21968 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21969 chi hbad
                ·
                  exact fin15Anchored_clause21970 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21971 chi hbad
                ·
                  exact fin15Anchored_clause21972 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21973 chi hbad
                ·
                  exact fin15Anchored_clause21974 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21975 chi hbad
                ·
                  exact fin15Anchored_clause21976 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21977 chi hbad
                ·
                  exact fin15Anchored_clause21978 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21979 chi hbad
                ·
                  exact fin15Anchored_clause21980 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21981 chi hbad
                ·
                  exact fin15Anchored_clause21982 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21983 chi hbad
                ·
                  exact fin15Anchored_clause21984 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21985 chi hbad
                ·
                  exact fin15Anchored_clause21986 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21987 chi hbad
                ·
                  exact fin15Anchored_clause21988 chi hbad
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
                  exact fin15Anchored_clause21989 chi hbad
                ·
                  exact fin15Anchored_clause21990 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21991 chi hbad
                ·
                  exact fin15Anchored_clause21992 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21993 chi hbad
                ·
                  exact fin15Anchored_clause21994 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21995 chi hbad
                ·
                  exact fin15Anchored_clause21996 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21997 chi hbad
                ·
                  exact fin15Anchored_clause21998 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause21999 chi hbad
                ·
                  exact fin15Anchored_clause22000 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22001 chi hbad
                ·
                  exact fin15Anchored_clause22002 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22003 chi hbad
                ·
                  exact fin15Anchored_clause22004 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22005 chi hbad
                ·
                  exact fin15Anchored_clause22006 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22007 chi hbad
                ·
                  exact fin15Anchored_clause22008 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22009 chi hbad
                ·
                  exact fin15Anchored_clause22010 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22011 chi hbad
                ·
                  exact fin15Anchored_clause22012 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22013 chi hbad
                ·
                  exact fin15Anchored_clause22014 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22015 chi hbad
                ·
                  exact fin15Anchored_clause22016 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22017 chi hbad
                ·
                  exact fin15Anchored_clause22018 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22019 chi hbad
                ·
                  exact fin15Anchored_clause22020 chi hbad
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
                exact fin15Anchored_clause22021 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22022 chi hbad
                ·
                  exact fin15Anchored_clause22023 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22024 chi hbad
                ·
                  exact fin15Anchored_clause22025 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22026 chi hbad
                ·
                  exact fin15Anchored_clause22027 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22028 chi hbad
                ·
                  exact fin15Anchored_clause22029 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22030 chi hbad
                ·
                  exact fin15Anchored_clause22031 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22032 chi hbad
                ·
                  exact fin15Anchored_clause22033 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22034 chi hbad
                ·
                  exact fin15Anchored_clause22035 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22036 chi hbad
                ·
                  exact fin15Anchored_clause22037 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22038 chi hbad
                ·
                  exact fin15Anchored_clause22039 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22040 chi hbad
                ·
                  exact fin15Anchored_clause22041 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22042 chi hbad
                ·
                  exact fin15Anchored_clause22043 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22044 chi hbad
                ·
                  exact fin15Anchored_clause22045 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22046 chi hbad
                ·
                  exact fin15Anchored_clause22047 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22048 chi hbad
                ·
                  exact fin15Anchored_clause22049 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22050 chi hbad
                ·
                  exact fin15Anchored_clause22051 chi hbad
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
                  exact fin15Anchored_clause22052 chi hbad
                ·
                  exact fin15Anchored_clause22053 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22054 chi hbad
                ·
                  exact fin15Anchored_clause22055 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22056 chi hbad
                ·
                  exact fin15Anchored_clause22057 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22058 chi hbad
                ·
                  exact fin15Anchored_clause22059 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22060 chi hbad
                ·
                  exact fin15Anchored_clause22061 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22062 chi hbad
                ·
                  exact fin15Anchored_clause22063 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22064 chi hbad
                ·
                  exact fin15Anchored_clause22065 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22066 chi hbad
                ·
                  exact fin15Anchored_clause22067 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22068 chi hbad
                ·
                  exact fin15Anchored_clause22069 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22070 chi hbad
                ·
                  exact fin15Anchored_clause22071 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22072 chi hbad
                ·
                  exact fin15Anchored_clause22073 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22074 chi hbad
                ·
                  exact fin15Anchored_clause22075 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22076 chi hbad
                ·
                  exact fin15Anchored_clause22077 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22078 chi hbad
                ·
                  exact fin15Anchored_clause22079 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22080 chi hbad
                ·
                  exact fin15Anchored_clause22081 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22082 chi hbad
                ·
                  exact fin15Anchored_clause22083 chi hbad
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
                exact fin15Anchored_clause22084 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22085 chi hbad
                ·
                  exact fin15Anchored_clause22086 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22087 chi hbad
                ·
                  exact fin15Anchored_clause22088 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22089 chi hbad
                ·
                  exact fin15Anchored_clause22090 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22091 chi hbad
                ·
                  exact fin15Anchored_clause22092 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22093 chi hbad
                ·
                  exact fin15Anchored_clause22094 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22095 chi hbad
                ·
                  exact fin15Anchored_clause22096 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22097 chi hbad
                ·
                  exact fin15Anchored_clause22098 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22099 chi hbad
                ·
                  exact fin15Anchored_clause22100 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22101 chi hbad
                ·
                  exact fin15Anchored_clause22102 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22103 chi hbad
                ·
                  exact fin15Anchored_clause22104 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22105 chi hbad
                ·
                  exact fin15Anchored_clause22106 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22107 chi hbad
                ·
                  exact fin15Anchored_clause22108 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22109 chi hbad
                ·
                  exact fin15Anchored_clause22110 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22111 chi hbad
                ·
                  exact fin15Anchored_clause22112 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22113 chi hbad
                ·
                  exact fin15Anchored_clause22114 chi hbad
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
                  exact fin15Anchored_clause22115 chi hbad
                ·
                  exact fin15Anchored_clause22116 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22117 chi hbad
                ·
                  exact fin15Anchored_clause22118 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22119 chi hbad
                ·
                  exact fin15Anchored_clause22120 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22121 chi hbad
                ·
                  exact fin15Anchored_clause22122 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22123 chi hbad
                ·
                  exact fin15Anchored_clause22124 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22125 chi hbad
                ·
                  exact fin15Anchored_clause22126 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22127 chi hbad
                ·
                  exact fin15Anchored_clause22128 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22129 chi hbad
                ·
                  exact fin15Anchored_clause22130 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22131 chi hbad
                ·
                  exact fin15Anchored_clause22132 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22133 chi hbad
                ·
                  exact fin15Anchored_clause22134 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22135 chi hbad
                ·
                  exact fin15Anchored_clause22136 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22137 chi hbad
                ·
                  exact fin15Anchored_clause22138 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22139 chi hbad
                ·
                  exact fin15Anchored_clause22140 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22141 chi hbad
                ·
                  exact fin15Anchored_clause22142 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22143 chi hbad
                ·
                  exact fin15Anchored_clause22144 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22145 chi hbad
                ·
                  exact fin15Anchored_clause22146 chi hbad
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
                  exact fin15Anchored_clause22147 chi hbad
                ·
                  exact fin15Anchored_clause22148 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22149 chi hbad
                ·
                  exact fin15Anchored_clause22150 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22151 chi hbad
                ·
                  exact fin15Anchored_clause22152 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22153 chi hbad
                ·
                  exact fin15Anchored_clause22154 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22155 chi hbad
                ·
                  exact fin15Anchored_clause22156 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22157 chi hbad
                ·
                  exact fin15Anchored_clause22158 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22159 chi hbad
                ·
                  exact fin15Anchored_clause22160 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22161 chi hbad
                ·
                  exact fin15Anchored_clause22162 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22163 chi hbad
                ·
                  exact fin15Anchored_clause22164 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22165 chi hbad
                ·
                  exact fin15Anchored_clause22166 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22167 chi hbad
                ·
                  exact fin15Anchored_clause22168 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22169 chi hbad
                ·
                  exact fin15Anchored_clause22170 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22171 chi hbad
                ·
                  exact fin15Anchored_clause22172 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22173 chi hbad
                ·
                  exact fin15Anchored_clause22174 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22175 chi hbad
                ·
                  exact fin15Anchored_clause22176 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22177 chi hbad
                ·
                  exact fin15Anchored_clause22178 chi hbad
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
                  exact fin15Anchored_clause22179 chi hbad
                ·
                  exact fin15Anchored_clause22180 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22181 chi hbad
                ·
                  exact fin15Anchored_clause22182 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22183 chi hbad
                ·
                  exact fin15Anchored_clause22184 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22185 chi hbad
                ·
                  exact fin15Anchored_clause22186 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22187 chi hbad
                ·
                  exact fin15Anchored_clause22188 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22189 chi hbad
                ·
                  exact fin15Anchored_clause22190 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22191 chi hbad
                ·
                  exact fin15Anchored_clause22192 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22193 chi hbad
                ·
                  exact fin15Anchored_clause22194 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22195 chi hbad
                ·
                  exact fin15Anchored_clause22196 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22197 chi hbad
                ·
                  exact fin15Anchored_clause22198 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22199 chi hbad
                ·
                  exact fin15Anchored_clause22200 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22201 chi hbad
                ·
                  exact fin15Anchored_clause22202 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22203 chi hbad
                ·
                  exact fin15Anchored_clause22204 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22205 chi hbad
                ·
                  exact fin15Anchored_clause22206 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22207 chi hbad
                ·
                  exact fin15Anchored_clause22208 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause22209 chi hbad
                ·
                  exact fin15Anchored_clause22210 chi hbad

end ErdosSzekeres

end
