module

public import ErdosSzekeres.Fin15AnchoredClauseChunk136
public import ErdosSzekeres.Fin15AnchoredClauseChunk137
public import ErdosSzekeres.Fin15AnchoredClauseChunk138

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 069. -/

theorem fin15Anchored_rejectSemanticSegment069
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2218 chi ∧
      ¬Fin15AnchoredAtom0556 chi) ∨
      ((¬Fin15AnchoredAtom2218 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom1217 chi) ∨
      (Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom0556 chi))) ∨
      (((Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom0561 chi) ∨
      (Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom0576 chi)) ∨
      ((Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom0712 chi) ∨
      (Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom1218 chi)))) ∨
      ((((¬Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom1218 chi) ∨
      (Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom0556 chi)) ∨
      ((Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom0562 chi) ∨
      (Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom0577 chi))) ∨
      (((Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom0713 chi) ∨
      (Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom1219 chi)) ∨
      ((¬Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom1219 chi) ∨
      (Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom0556 chi))))) ∨
      (((((Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom0563 chi) ∨
      (Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom0578 chi)) ∨
      ((Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom0714 chi) ∨
      (Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom1220 chi))) ∨
      (((¬Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom1220 chi) ∨
      (Fin15AnchoredAtom2222 chi ∧
      ¬Fin15AnchoredAtom0558 chi)) ∨
      ((Fin15AnchoredAtom2222 chi ∧
      ¬Fin15AnchoredAtom0579 chi) ∨
      (Fin15AnchoredAtom2222 chi ∧
      ¬Fin15AnchoredAtom0715 chi)))) ∨
      ((((Fin15AnchoredAtom2222 chi ∧
      ¬Fin15AnchoredAtom1221 chi) ∨
      (¬Fin15AnchoredAtom2222 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom1221 chi)) ∨
      ((Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom0557 chi) ∨
      (Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom0559 chi))) ∨
      (((Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom0580 chi) ∨
      (Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom0716 chi)) ∨
      ((Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom1222 chi) ∨
      (¬Fin15AnchoredAtom2223 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom1222 chi)))))) ∨
      ((((((Fin15AnchoredAtom2225 chi ∧
      ¬Fin15AnchoredAtom0561 chi) ∨
      (Fin15AnchoredAtom2226 chi ∧
      ¬Fin15AnchoredAtom0557 chi)) ∨
      ((Fin15AnchoredAtom2226 chi ∧
      ¬Fin15AnchoredAtom0562 chi) ∨
      (Fin15AnchoredAtom2226 chi ∧
      ¬Fin15AnchoredAtom0719 chi))) ∨
      (((¬Fin15AnchoredAtom2227 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom1226 chi) ∨
      (Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom0558 chi)) ∨
      ((Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom0559 chi) ∨
      (Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom0585 chi)))) ∨
      ((((Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom0721 chi) ∨
      (Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom1227 chi)) ∨
      ((¬Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom1227 chi) ∨
      (Fin15AnchoredAtom2229 chi ∧
      ¬Fin15AnchoredAtom0558 chi))) ∨
      (((Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom0558 chi) ∨
      (Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom0561 chi)) ∨
      ((Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom0587 chi) ∨
      (Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom0723 chi))))) ∨
      (((((Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom1229 chi) ∨
      (¬Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom1229 chi)) ∨
      ((Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom0558 chi) ∨
      (Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom0562 chi))) ∨
      (((Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom0588 chi) ∨
      (Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom0724 chi)) ∨
      ((Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom1230 chi) ∨
      (¬Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom1230 chi)))) ∨
      ((((Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom0558 chi) ∨
      (Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom0563 chi)) ∨
      ((Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom0589 chi) ∨
      (Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom0725 chi))) ∨
      (((Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom1231 chi) ∨
      (¬Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom1231 chi)) ∨
      ((Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom0559 chi) ∨
      (Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom0560 chi))))))) ∨
      ((((((Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom0590 chi) ∨
      ((Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom0726 chi) ∨
      (Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom1232 chi))) ∨
      (((¬Fin15AnchoredAtom2233 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom1232 chi) ∨
      (Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom0559 chi)) ∨
      ((Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom0561 chi) ∨
      (Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom0591 chi)))) ∨
      ((((Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom0727 chi) ∨
      (Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom1233 chi)) ∨
      ((¬Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom1233 chi) ∨
      (Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom0559 chi))) ∨
      (((Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom0562 chi) ∨
      (Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom0592 chi)) ∨
      ((Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom0728 chi) ∨
      (Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom1234 chi))))) ∨
      (((((¬Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom1234 chi) ∨
      (Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom0559 chi)) ∨
      ((Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom0563 chi) ∨
      (Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom0593 chi))) ∨
      (((Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom0729 chi) ∨
      (Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom1235 chi)) ∨
      ((¬Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom1235 chi) ∨
      (Fin15AnchoredAtom2237 chi ∧
      ¬Fin15AnchoredAtom0561 chi)))) ∨
      ((((¬Fin15AnchoredAtom2237 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom1236 chi) ∨
      (Fin15AnchoredAtom2238 chi ∧
      ¬Fin15AnchoredAtom0560 chi)) ∨
      ((Fin15AnchoredAtom2238 chi ∧
      ¬Fin15AnchoredAtom0562 chi) ∨
      (Fin15AnchoredAtom2238 chi ∧
      ¬Fin15AnchoredAtom1237 chi))) ∨
      (((¬Fin15AnchoredAtom2238 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom1237 chi) ∨
      (Fin15AnchoredAtom2239 chi ∧
      ¬Fin15AnchoredAtom0563 chi)) ∨
      ((Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom0561 chi) ∨
      (Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom0562 chi)))))) ∨
      ((((((Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom0597 chi) ∨
      (Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom0733 chi)) ∨
      ((Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom1239 chi) ∨
      (¬Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom1239 chi))) ∨
      (((Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom0561 chi) ∨
      (Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom0563 chi)) ∨
      ((Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom0598 chi) ∨
      (Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom0734 chi)))) ∨
      ((((Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom1240 chi) ∨
      (¬Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom1240 chi)) ∨
      ((Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom0562 chi) ∨
      (Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom0563 chi))) ∨
      (((Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom0599 chi) ∨
      (Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom0735 chi)) ∨
      ((Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom1241 chi) ∨
      (¬Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom1241 chi))))) ∨
      (((((Fin15AnchoredAtom2243 chi ∧
      ¬Fin15AnchoredAtom0564 chi) ∨
      (Fin15AnchoredAtom2243 chi ∧
      ¬Fin15AnchoredAtom1242 chi)) ∨
      ((¬Fin15AnchoredAtom2243 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom1242 chi) ∨
      (Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom0564 chi))) ∨
      (((Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom0566 chi) ∨
      (Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom0573 chi)) ∨
      ((Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom0737 chi) ∨
      (Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom1243 chi)))) ∨
      ((((¬Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom1243 chi) ∨
      (Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom0564 chi)) ∨
      ((Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom0567 chi) ∨
      (Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom0574 chi))) ∨
      (((Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom0738 chi) ∨
      (Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom1244 chi)) ∨
      ((¬Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom1244 chi) ∨
      (Fin15AnchoredAtom2246 chi ∧
      ¬Fin15AnchoredAtom0568 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2246 chi ∧
      ¬Fin15AnchoredAtom0575 chi) ∨
      ((Fin15AnchoredAtom2246 chi ∧
      ¬Fin15AnchoredAtom0739 chi) ∨
      (¬Fin15AnchoredAtom2246 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom1245 chi))) ∨
      (((Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom0564 chi) ∨
      (Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom0569 chi)) ∨
      ((Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom0576 chi) ∨
      (Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom0740 chi)))) ∨
      ((((Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom1246 chi) ∨
      (¬Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom1246 chi)) ∨
      ((Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom0564 chi) ∨
      (Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom0570 chi))) ∨
      (((Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom0577 chi) ∨
      (Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom0741 chi)) ∨
      ((Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom1247 chi) ∨
      (¬Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom1247 chi))))) ∨
      (((((Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom0564 chi) ∨
      (Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom0571 chi)) ∨
      ((Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom0578 chi) ∨
      (Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom0742 chi))) ∨
      (((Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom1248 chi) ∨
      (¬Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom1248 chi)) ∨
      ((Fin15AnchoredAtom2250 chi ∧
      ¬Fin15AnchoredAtom0566 chi) ∨
      (Fin15AnchoredAtom2250 chi ∧
      ¬Fin15AnchoredAtom0579 chi)))) ∨
      ((((Fin15AnchoredAtom2250 chi ∧
      ¬Fin15AnchoredAtom1249 chi) ∨
      (¬Fin15AnchoredAtom2250 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom1249 chi)) ∨
      ((Fin15AnchoredAtom2251 chi ∧
      ¬Fin15AnchoredAtom0567 chi) ∨
      (Fin15AnchoredAtom2251 chi ∧
      ¬Fin15AnchoredAtom1250 chi))) ∨
      (((¬Fin15AnchoredAtom2251 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom1250 chi) ∨
      (Fin15AnchoredAtom2253 chi ∧
      ¬Fin15AnchoredAtom0569 chi)) ∨
      ((Fin15AnchoredAtom2253 chi ∧
      ¬Fin15AnchoredAtom1252 chi) ∨
      (¬Fin15AnchoredAtom2253 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0582 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom1252 chi)))))) ∨
      ((((((Fin15AnchoredAtom2254 chi ∧
      ¬Fin15AnchoredAtom0570 chi) ∨
      (Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom0566 chi)) ∨
      ((Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom0567 chi) ∨
      (Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom0585 chi))) ∨
      (((Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom0749 chi) ∨
      (Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom1255 chi)) ∨
      ((¬Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom1255 chi) ∨
      (Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom0566 chi)))) ∨
      ((((Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom0568 chi) ∨
      (Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom0586 chi)) ∨
      ((Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom0750 chi) ∨
      (Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom1256 chi))) ∨
      (((¬Fin15AnchoredAtom2257 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom1256 chi) ∨
      (Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom0566 chi)) ∨
      ((Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom0569 chi) ∨
      (Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom0587 chi))))) ∨
      (((((Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom0751 chi) ∨
      (Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom1257 chi)) ∨
      ((¬Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom1257 chi) ∨
      (Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom0566 chi))) ∨
      (((Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom0570 chi) ∨
      (Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom0588 chi)) ∨
      ((Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom0752 chi) ∨
      (Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom1258 chi)))) ∨
      ((((¬Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom1258 chi) ∨
      (Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom0566 chi)) ∨
      ((Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom0571 chi) ∨
      (Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom0589 chi))) ∨
      (((Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom0753 chi) ∨
      (Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom1259 chi)) ∨
      ((¬Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom1259 chi) ∨
      (Fin15AnchoredAtom2261 chi ∧
      ¬Fin15AnchoredAtom0567 chi))))))) ∨
      (((((((Fin15AnchoredAtom2261 chi ∧
      ¬Fin15AnchoredAtom0590 chi) ∨
      (Fin15AnchoredAtom2261 chi ∧
      ¬Fin15AnchoredAtom0754 chi)) ∨
      ((Fin15AnchoredAtom2261 chi ∧
      ¬Fin15AnchoredAtom1260 chi) ∨
      (¬Fin15AnchoredAtom2261 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom1260 chi))) ∨
      (((Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom0567 chi) ∨
      (Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom0569 chi)) ∨
      ((Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom0591 chi) ∨
      (Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom0755 chi)))) ∨
      ((((Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom1261 chi) ∨
      (¬Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom1261 chi)) ∨
      ((Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom0567 chi) ∨
      (Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom0570 chi))) ∨
      (((Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom0592 chi) ∨
      (Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom0756 chi)) ∨
      ((Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom1262 chi) ∨
      (¬Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom1262 chi))))) ∨
      (((((Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom0567 chi) ∨
      (Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom0571 chi)) ∨
      ((Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom0593 chi) ∨
      (Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom0757 chi))) ∨
      (((Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom1263 chi) ∨
      (¬Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom1263 chi)) ∨
      ((Fin15AnchoredAtom2265 chi ∧
      ¬Fin15AnchoredAtom0568 chi) ∨
      (Fin15AnchoredAtom2265 chi ∧
      ¬Fin15AnchoredAtom0569 chi)))) ∨
      ((((Fin15AnchoredAtom2265 chi ∧
      ¬Fin15AnchoredAtom0594 chi) ∨
      (Fin15AnchoredAtom2265 chi ∧
      ¬Fin15AnchoredAtom0758 chi)) ∨
      ((Fin15AnchoredAtom2266 chi ∧
      ¬Fin15AnchoredAtom0570 chi) ∨
      (Fin15AnchoredAtom2266 chi ∧
      ¬Fin15AnchoredAtom0759 chi))) ∨
      (((Fin15AnchoredAtom2266 chi ∧
      ¬Fin15AnchoredAtom1265 chi) ∨
      (¬Fin15AnchoredAtom2266 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom1265 chi)) ∨
      ((Fin15AnchoredAtom2267 chi ∧
      ¬Fin15AnchoredAtom0571 chi) ∨
      (Fin15AnchoredAtom2267 chi ∧
      ¬Fin15AnchoredAtom1266 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2267 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom1266 chi) ∨
      (Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom0569 chi)) ∨
      ((Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom0570 chi) ∨
      (Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom0597 chi))) ∨
      (((Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom0761 chi) ∨
      (Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom1267 chi)) ∨
      ((¬Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom1267 chi) ∨
      (Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom0569 chi)))) ∨
      ((((Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom0571 chi) ∨
      (Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom0598 chi)) ∨
      ((Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom0762 chi) ∨
      (Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom1268 chi))) ∨
      (((¬Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom1268 chi) ∨
      (Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom0570 chi)) ∨
      ((Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom0571 chi) ∨
      (Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom0599 chi))))) ∨
      (((((Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom0763 chi) ∨
      (Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom1269 chi)) ∨
      ((¬Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom1269 chi) ∨
      (Fin15AnchoredAtom2271 chi ∧
      ¬Fin15AnchoredAtom0573 chi))) ∨
      (((Fin15AnchoredAtom2272 chi ∧
      ¬Fin15AnchoredAtom0572 chi) ∨
      (Fin15AnchoredAtom2272 chi ∧
      ¬Fin15AnchoredAtom0574 chi)) ∨
      ((Fin15AnchoredAtom2272 chi ∧
      ¬Fin15AnchoredAtom1271 chi) ∨
      (¬Fin15AnchoredAtom2272 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1271 chi)))) ∨
      ((((Fin15AnchoredAtom2274 chi ∧
      ¬Fin15AnchoredAtom0576 chi) ∨
      (Fin15AnchoredAtom2275 chi ∧
      ¬Fin15AnchoredAtom0577 chi)) ∨
      ((Fin15AnchoredAtom2276 chi ∧
      ¬Fin15AnchoredAtom0578 chi) ∨
      (¬Fin15AnchoredAtom2276 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1275 chi))) ∨
      (((Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom0573 chi) ∨
      (Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom0574 chi)) ∨
      ((Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom0585 chi) ∨
      (Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom0770 chi)))))))))) := by
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
                exact fin15Anchored_clause17415 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17416 chi hbad
                ·
                  exact fin15Anchored_clause17417 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17418 chi hbad
                ·
                  exact fin15Anchored_clause17419 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17420 chi hbad
                ·
                  exact fin15Anchored_clause17421 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17422 chi hbad
                ·
                  exact fin15Anchored_clause17423 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17424 chi hbad
                ·
                  exact fin15Anchored_clause17425 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17426 chi hbad
                ·
                  exact fin15Anchored_clause17427 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17428 chi hbad
                ·
                  exact fin15Anchored_clause17429 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17430 chi hbad
                ·
                  exact fin15Anchored_clause17431 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17432 chi hbad
                ·
                  exact fin15Anchored_clause17433 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17434 chi hbad
                ·
                  exact fin15Anchored_clause17435 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17436 chi hbad
                ·
                  exact fin15Anchored_clause17437 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17438 chi hbad
                ·
                  exact fin15Anchored_clause17439 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17440 chi hbad
                ·
                  exact fin15Anchored_clause17441 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17442 chi hbad
                ·
                  exact fin15Anchored_clause17443 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17444 chi hbad
                ·
                  exact fin15Anchored_clause17445 chi hbad
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
                  exact fin15Anchored_clause17446 chi hbad
                ·
                  exact fin15Anchored_clause17447 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17448 chi hbad
                ·
                  exact fin15Anchored_clause17449 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17450 chi hbad
                ·
                  exact fin15Anchored_clause17451 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17452 chi hbad
                ·
                  exact fin15Anchored_clause17453 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17454 chi hbad
                ·
                  exact fin15Anchored_clause17455 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17456 chi hbad
                ·
                  exact fin15Anchored_clause17457 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17458 chi hbad
                ·
                  exact fin15Anchored_clause17459 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17460 chi hbad
                ·
                  exact fin15Anchored_clause17461 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17462 chi hbad
                ·
                  exact fin15Anchored_clause17463 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17464 chi hbad
                ·
                  exact fin15Anchored_clause17465 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17466 chi hbad
                ·
                  exact fin15Anchored_clause17467 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17468 chi hbad
                ·
                  exact fin15Anchored_clause17469 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17470 chi hbad
                ·
                  exact fin15Anchored_clause17471 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17472 chi hbad
                ·
                  exact fin15Anchored_clause17473 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17474 chi hbad
                ·
                  exact fin15Anchored_clause17475 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17476 chi hbad
                ·
                  exact fin15Anchored_clause17477 chi hbad
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
                exact fin15Anchored_clause17478 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17479 chi hbad
                ·
                  exact fin15Anchored_clause17480 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17481 chi hbad
                ·
                  exact fin15Anchored_clause17482 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17483 chi hbad
                ·
                  exact fin15Anchored_clause17484 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17485 chi hbad
                ·
                  exact fin15Anchored_clause17486 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17487 chi hbad
                ·
                  exact fin15Anchored_clause17488 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17489 chi hbad
                ·
                  exact fin15Anchored_clause17490 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17491 chi hbad
                ·
                  exact fin15Anchored_clause17492 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17493 chi hbad
                ·
                  exact fin15Anchored_clause17494 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17495 chi hbad
                ·
                  exact fin15Anchored_clause17496 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17497 chi hbad
                ·
                  exact fin15Anchored_clause17498 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17499 chi hbad
                ·
                  exact fin15Anchored_clause17500 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17501 chi hbad
                ·
                  exact fin15Anchored_clause17502 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17503 chi hbad
                ·
                  exact fin15Anchored_clause17504 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17505 chi hbad
                ·
                  exact fin15Anchored_clause17506 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17507 chi hbad
                ·
                  exact fin15Anchored_clause17508 chi hbad
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
                  exact fin15Anchored_clause17509 chi hbad
                ·
                  exact fin15Anchored_clause17510 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17511 chi hbad
                ·
                  exact fin15Anchored_clause17512 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17513 chi hbad
                ·
                  exact fin15Anchored_clause17514 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17515 chi hbad
                ·
                  exact fin15Anchored_clause17516 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17517 chi hbad
                ·
                  exact fin15Anchored_clause17518 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17519 chi hbad
                ·
                  exact fin15Anchored_clause17520 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17521 chi hbad
                ·
                  exact fin15Anchored_clause17522 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17523 chi hbad
                ·
                  exact fin15Anchored_clause17524 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17525 chi hbad
                ·
                  exact fin15Anchored_clause17526 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17527 chi hbad
                ·
                  exact fin15Anchored_clause17528 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17529 chi hbad
                ·
                  exact fin15Anchored_clause17530 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17531 chi hbad
                ·
                  exact fin15Anchored_clause17532 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17533 chi hbad
                ·
                  exact fin15Anchored_clause17534 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17535 chi hbad
                ·
                  exact fin15Anchored_clause17536 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17537 chi hbad
                ·
                  exact fin15Anchored_clause17538 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17539 chi hbad
                ·
                  exact fin15Anchored_clause17540 chi hbad
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
                exact fin15Anchored_clause17541 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17542 chi hbad
                ·
                  exact fin15Anchored_clause17543 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17544 chi hbad
                ·
                  exact fin15Anchored_clause17545 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17546 chi hbad
                ·
                  exact fin15Anchored_clause17547 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17548 chi hbad
                ·
                  exact fin15Anchored_clause17549 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17550 chi hbad
                ·
                  exact fin15Anchored_clause17551 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17552 chi hbad
                ·
                  exact fin15Anchored_clause17553 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17554 chi hbad
                ·
                  exact fin15Anchored_clause17555 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17556 chi hbad
                ·
                  exact fin15Anchored_clause17557 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17558 chi hbad
                ·
                  exact fin15Anchored_clause17559 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17560 chi hbad
                ·
                  exact fin15Anchored_clause17561 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17562 chi hbad
                ·
                  exact fin15Anchored_clause17563 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17564 chi hbad
                ·
                  exact fin15Anchored_clause17565 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17566 chi hbad
                ·
                  exact fin15Anchored_clause17567 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17568 chi hbad
                ·
                  exact fin15Anchored_clause17569 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17570 chi hbad
                ·
                  exact fin15Anchored_clause17571 chi hbad
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
                  exact fin15Anchored_clause17572 chi hbad
                ·
                  exact fin15Anchored_clause17573 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17574 chi hbad
                ·
                  exact fin15Anchored_clause17575 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17576 chi hbad
                ·
                  exact fin15Anchored_clause17577 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17578 chi hbad
                ·
                  exact fin15Anchored_clause17579 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17580 chi hbad
                ·
                  exact fin15Anchored_clause17581 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17582 chi hbad
                ·
                  exact fin15Anchored_clause17583 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17584 chi hbad
                ·
                  exact fin15Anchored_clause17585 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17586 chi hbad
                ·
                  exact fin15Anchored_clause17587 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17588 chi hbad
                ·
                  exact fin15Anchored_clause17589 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17590 chi hbad
                ·
                  exact fin15Anchored_clause17591 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17592 chi hbad
                ·
                  exact fin15Anchored_clause17593 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17594 chi hbad
                ·
                  exact fin15Anchored_clause17595 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17596 chi hbad
                ·
                  exact fin15Anchored_clause17597 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17598 chi hbad
                ·
                  exact fin15Anchored_clause17599 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17600 chi hbad
                ·
                  exact fin15Anchored_clause17601 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17602 chi hbad
                ·
                  exact fin15Anchored_clause17603 chi hbad
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
                  exact fin15Anchored_clause17604 chi hbad
                ·
                  exact fin15Anchored_clause17605 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17606 chi hbad
                ·
                  exact fin15Anchored_clause17607 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17608 chi hbad
                ·
                  exact fin15Anchored_clause17609 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17610 chi hbad
                ·
                  exact fin15Anchored_clause17611 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17612 chi hbad
                ·
                  exact fin15Anchored_clause17613 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17614 chi hbad
                ·
                  exact fin15Anchored_clause17615 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17616 chi hbad
                ·
                  exact fin15Anchored_clause17617 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17618 chi hbad
                ·
                  exact fin15Anchored_clause17619 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17620 chi hbad
                ·
                  exact fin15Anchored_clause17621 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17622 chi hbad
                ·
                  exact fin15Anchored_clause17623 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17624 chi hbad
                ·
                  exact fin15Anchored_clause17625 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17626 chi hbad
                ·
                  exact fin15Anchored_clause17627 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17628 chi hbad
                ·
                  exact fin15Anchored_clause17629 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17630 chi hbad
                ·
                  exact fin15Anchored_clause17631 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17632 chi hbad
                ·
                  exact fin15Anchored_clause17633 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17634 chi hbad
                ·
                  exact fin15Anchored_clause17635 chi hbad
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
                  exact fin15Anchored_clause17636 chi hbad
                ·
                  exact fin15Anchored_clause17637 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17638 chi hbad
                ·
                  exact fin15Anchored_clause17639 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17640 chi hbad
                ·
                  exact fin15Anchored_clause17641 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17642 chi hbad
                ·
                  exact fin15Anchored_clause17643 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17644 chi hbad
                ·
                  exact fin15Anchored_clause17645 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17646 chi hbad
                ·
                  exact fin15Anchored_clause17647 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17648 chi hbad
                ·
                  exact fin15Anchored_clause17649 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17650 chi hbad
                ·
                  exact fin15Anchored_clause17651 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17652 chi hbad
                ·
                  exact fin15Anchored_clause17653 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17654 chi hbad
                ·
                  exact fin15Anchored_clause17655 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17656 chi hbad
                ·
                  exact fin15Anchored_clause17657 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17658 chi hbad
                ·
                  exact fin15Anchored_clause17659 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17660 chi hbad
                ·
                  exact fin15Anchored_clause17661 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17662 chi hbad
                ·
                  exact fin15Anchored_clause17663 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17664 chi hbad
                ·
                  exact fin15Anchored_clause17665 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17666 chi hbad
                ·
                  exact fin15Anchored_clause17667 chi hbad

end ErdosSzekeres

end
