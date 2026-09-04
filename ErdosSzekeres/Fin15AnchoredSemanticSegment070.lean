module

public import ErdosSzekeres.Fin15AnchoredClauseChunk138
public import ErdosSzekeres.Fin15AnchoredClauseChunk139

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 070. -/

theorem fin15Anchored_rejectSemanticSegment070
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom1276 chi) ∨
      ((¬Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1276 chi) ∨
      (Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom0573 chi))) ∨
      (((Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom0575 chi) ∨
      (Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom0586 chi)) ∨
      ((Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom0771 chi) ∨
      (Fin15AnchoredAtom2278 chi ∧
      ¬Fin15AnchoredAtom1277 chi)))) ∨
      ((((¬Fin15AnchoredAtom2278 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom1277 chi) ∨
      (Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom0573 chi)) ∨
      ((Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom0576 chi) ∨
      (Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom0587 chi))) ∨
      (((Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom0772 chi) ∨
      (Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom1278 chi)) ∨
      ((¬Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1278 chi) ∨
      (Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom0573 chi))))) ∨
      (((((Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom0577 chi) ∨
      (Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom0588 chi)) ∨
      ((Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom0773 chi) ∨
      (Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom1279 chi))) ∨
      (((¬Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1279 chi) ∨
      (Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom0573 chi)) ∨
      ((Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom0578 chi) ∨
      (Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom0589 chi)))) ∨
      ((((Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom0774 chi) ∨
      (Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom1280 chi)) ∨
      ((¬Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1280 chi) ∨
      (Fin15AnchoredAtom2282 chi ∧
      ¬Fin15AnchoredAtom0775 chi))) ∨
      (((Fin15AnchoredAtom2282 chi ∧
      ¬Fin15AnchoredAtom1281 chi) ∨
      (¬Fin15AnchoredAtom2282 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom1281 chi)) ∨
      ((Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom0574 chi) ∨
      (Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom0576 chi)))))) ∨
      ((((((Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom0591 chi) ∨
      (Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom0776 chi)) ∨
      ((Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom1282 chi) ∨
      (¬Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1282 chi))) ∨
      (((Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom0574 chi) ∨
      (Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom0577 chi)) ∨
      ((Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom0592 chi) ∨
      (Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom0777 chi)))) ∨
      ((((Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom1283 chi) ∨
      (¬Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1283 chi)) ∨
      ((Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom0574 chi) ∨
      (Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom0578 chi))) ∨
      (((Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom0593 chi) ∨
      (Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom0778 chi)) ∨
      ((Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom1284 chi) ∨
      (¬Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1284 chi))))) ∨
      (((((Fin15AnchoredAtom2286 chi ∧
      ¬Fin15AnchoredAtom0576 chi) ∨
      (Fin15AnchoredAtom2286 chi ∧
      ¬Fin15AnchoredAtom0594 chi)) ∨
      ((Fin15AnchoredAtom2286 chi ∧
      ¬Fin15AnchoredAtom0779 chi) ∨
      (Fin15AnchoredAtom2286 chi ∧
      ¬Fin15AnchoredAtom1285 chi))) ∨
      (((¬Fin15AnchoredAtom2286 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom1285 chi) ∨
      (Fin15AnchoredAtom2287 chi ∧
      ¬Fin15AnchoredAtom0575 chi)) ∨
      ((Fin15AnchoredAtom2287 chi ∧
      ¬Fin15AnchoredAtom0577 chi) ∨
      (Fin15AnchoredAtom2287 chi ∧
      ¬Fin15AnchoredAtom0780 chi)))) ∨
      ((((¬Fin15AnchoredAtom2287 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom1286 chi) ∨
      (Fin15AnchoredAtom2288 chi ∧
      ¬Fin15AnchoredAtom0578 chi)) ∨
      ((Fin15AnchoredAtom2288 chi ∧
      ¬Fin15AnchoredAtom0781 chi) ∨
      (Fin15AnchoredAtom2288 chi ∧
      ¬Fin15AnchoredAtom1287 chi))) ∨
      (((¬Fin15AnchoredAtom2288 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom1287 chi) ∨
      (Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom0576 chi)) ∨
      ((Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom0577 chi) ∨
      (Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom0597 chi))))))) ∨
      ((((((Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom0782 chi) ∨
      ((Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom1288 chi) ∨
      (¬Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1288 chi))) ∨
      (((Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom0576 chi) ∨
      (Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom0578 chi)) ∨
      ((Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom0598 chi) ∨
      (Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom0783 chi)))) ∨
      ((((Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom1289 chi) ∨
      (¬Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1289 chi)) ∨
      ((Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom0577 chi) ∨
      (Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom0578 chi))) ∨
      (((Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom0599 chi) ∨
      (Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom0784 chi)) ∨
      ((Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom1290 chi) ∨
      (¬Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1290 chi))))) ∨
      (((((Fin15AnchoredAtom2292 chi ∧
      ¬Fin15AnchoredAtom0580 chi) ∨
      (Fin15AnchoredAtom2292 chi ∧
      ¬Fin15AnchoredAtom0585 chi)) ∨
      ((¬Fin15AnchoredAtom2292 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1291 chi) ∨
      (Fin15AnchoredAtom2294 chi ∧
      ¬Fin15AnchoredAtom0579 chi))) ∨
      (((Fin15AnchoredAtom2294 chi ∧
      ¬Fin15AnchoredAtom0582 chi) ∨
      (Fin15AnchoredAtom2296 chi ∧
      ¬Fin15AnchoredAtom0589 chi)) ∨
      ((Fin15AnchoredAtom2298 chi ∧
      ¬Fin15AnchoredAtom0580 chi) ∨
      (Fin15AnchoredAtom2299 chi ∧
      ¬Fin15AnchoredAtom0580 chi)))) ∨
      ((((Fin15AnchoredAtom2299 chi ∧
      ¬Fin15AnchoredAtom0792 chi) ∨
      (Fin15AnchoredAtom2304 chi ∧
      ¬Fin15AnchoredAtom0797 chi)) ∨
      ((Fin15AnchoredAtom2305 chi ∧
      ¬Fin15AnchoredAtom0598 chi) ∨
      (¬Fin15AnchoredAtom2305 chi ∧
      Fin15AnchoredAtom0582 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1304 chi))) ∨
      (((Fin15AnchoredAtom2307 chi ∧
      ¬Fin15AnchoredAtom0585 chi) ∨
      (Fin15AnchoredAtom2307 chi ∧
      ¬Fin15AnchoredAtom0800 chi)) ∨
      ((Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom0585 chi) ∨
      (Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom0587 chi)))))) ∨
      ((((((Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom0591 chi) ∨
      (Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom0801 chi)) ∨
      ((Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom1307 chi) ∨
      (¬Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1307 chi))) ∨
      (((Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom0585 chi) ∨
      (Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom0588 chi)) ∨
      ((Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom0592 chi) ∨
      (Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom0802 chi)))) ∨
      ((((Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom1308 chi) ∨
      (¬Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1308 chi)) ∨
      ((Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom0585 chi) ∨
      (Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom0589 chi))) ∨
      (((Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom0593 chi) ∨
      (Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom0803 chi)) ∨
      ((Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom1309 chi) ∨
      (¬Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1309 chi))))) ∨
      (((((Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom0586 chi) ∨
      (Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom0587 chi)) ∨
      ((Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom0594 chi) ∨
      (Fin15AnchoredAtom2311 chi ∧
      ¬Fin15AnchoredAtom0804 chi))) ∨
      (((¬Fin15AnchoredAtom2311 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1310 chi) ∨
      (Fin15AnchoredAtom2312 chi ∧
      ¬Fin15AnchoredAtom0586 chi)) ∨
      ((Fin15AnchoredAtom2312 chi ∧
      ¬Fin15AnchoredAtom0588 chi) ∨
      (Fin15AnchoredAtom2312 chi ∧
      ¬Fin15AnchoredAtom0805 chi)))) ∨
      ((((¬Fin15AnchoredAtom2312 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1311 chi) ∨
      (Fin15AnchoredAtom2313 chi ∧
      ¬Fin15AnchoredAtom0589 chi)) ∨
      ((Fin15AnchoredAtom2313 chi ∧
      ¬Fin15AnchoredAtom0596 chi) ∨
      (Fin15AnchoredAtom2313 chi ∧
      ¬Fin15AnchoredAtom0806 chi))) ∨
      (((Fin15AnchoredAtom2313 chi ∧
      ¬Fin15AnchoredAtom1312 chi) ∨
      (¬Fin15AnchoredAtom2313 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom1312 chi)) ∨
      ((Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom0587 chi) ∨
      (Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom0588 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom0597 chi) ∨
      ((Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom0807 chi) ∨
      (Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom1313 chi))) ∨
      (((¬Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1313 chi) ∨
      (Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom0587 chi)) ∨
      ((Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom0589 chi) ∨
      (Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom0598 chi)))) ∨
      ((((Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom0808 chi) ∨
      (Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom1314 chi)) ∨
      ((¬Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1314 chi) ∨
      (Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom0588 chi))) ∨
      (((Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom0589 chi) ∨
      (Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom0599 chi)) ∨
      ((Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom0809 chi) ∨
      (Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom1315 chi))))) ∨
      (((((¬Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1315 chi) ∨
      (Fin15AnchoredAtom2317 chi ∧
      ¬Fin15AnchoredAtom0590 chi)) ∨
      ((Fin15AnchoredAtom2317 chi ∧
      ¬Fin15AnchoredAtom0591 chi) ∨
      (¬Fin15AnchoredAtom2317 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1316 chi))) ∨
      (((Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom0590 chi) ∨
      (Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom0592 chi)) ∨
      ((Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom0595 chi) ∨
      (Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom0811 chi)))) ∨
      ((((Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom1317 chi) ∨
      (Fin15AnchoredAtom2319 chi ∧
      ¬Fin15AnchoredAtom0593 chi)) ∨
      ((Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom0591 chi) ∨
      (Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom0592 chi))) ∨
      (((Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom0597 chi) ∨
      (Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom0813 chi)) ∨
      ((Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom1319 chi) ∨
      (¬Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1319 chi)))))) ∨
      ((((((Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom0591 chi) ∨
      (Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom0593 chi)) ∨
      ((Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom0598 chi) ∨
      (Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom0814 chi))) ∨
      (((Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom1320 chi) ∨
      (¬Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1320 chi)) ∨
      ((Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom0592 chi) ∨
      (Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom0593 chi)))) ∨
      ((((Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom0599 chi) ∨
      (Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom0815 chi)) ∨
      ((Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom1321 chi) ∨
      (¬Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1321 chi))) ∨
      (((Fin15AnchoredAtom2323 chi ∧
      ¬Fin15AnchoredAtom0597 chi) ∨
      (Fin15AnchoredAtom2323 chi ∧
      ¬Fin15AnchoredAtom0816 chi)) ∨
      ((Fin15AnchoredAtom2324 chi ∧
      ¬Fin15AnchoredAtom0598 chi) ∨
      (Fin15AnchoredAtom2324 chi ∧
      ¬Fin15AnchoredAtom0817 chi))))) ∨
      (((((¬Fin15AnchoredAtom2324 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1323 chi) ∨
      (Fin15AnchoredAtom2325 chi ∧
      ¬Fin15AnchoredAtom0599 chi)) ∨
      ((Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom0597 chi) ∨
      (Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom0598 chi))) ∨
      (((Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom0599 chi) ∨
      (Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom0819 chi)) ∨
      ((Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom1325 chi) ∨
      (¬Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1325 chi)))) ∨
      ((((Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom0600 chi) ∨
      (Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom0601 chi)) ∨
      ((Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom0610 chi) ∨
      (Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom0655 chi))) ∨
      (((Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom1326 chi) ∨
      (¬Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom1326 chi)) ∨
      ((Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom0600 chi) ∨
      (Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom0602 chi))))))) ∨
      ((((((Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom0611 chi) ∨
      ((Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom0656 chi) ∨
      (Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom1327 chi))) ∨
      (((¬Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom1327 chi) ∨
      (Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom0600 chi)) ∨
      ((Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom0603 chi) ∨
      (Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom0612 chi)))) ∨
      ((((Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom0657 chi) ∨
      (Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom1328 chi)) ∨
      ((¬Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom1328 chi) ∨
      (Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom0600 chi))) ∨
      (((Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom0604 chi) ∨
      (Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom0613 chi)) ∨
      ((Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom0658 chi) ∨
      (Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom1329 chi))))) ∨
      (((((¬Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom1329 chi) ∨
      (Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom0600 chi)) ∨
      ((Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom0605 chi) ∨
      (Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom0614 chi))) ∨
      (((Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom0659 chi) ∨
      (Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom1330 chi)) ∨
      ((¬Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom1330 chi) ∨
      (Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom0600 chi)))) ∨
      ((((Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom0606 chi) ∨
      (Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom0615 chi)) ∨
      ((Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom0660 chi) ∨
      (Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom1331 chi))) ∨
      (((¬Fin15AnchoredAtom2332 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom1331 chi) ∨
      (Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom0600 chi)) ∨
      ((Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom0607 chi) ∨
      (Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom0616 chi)))))) ∨
      ((((((Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom0661 chi) ∨
      (Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom1332 chi)) ∨
      ((¬Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom1332 chi) ∨
      (Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom0600 chi))) ∨
      (((Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom0608 chi) ∨
      (Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom0617 chi)) ∨
      ((Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom0662 chi) ∨
      (Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom1333 chi)))) ∨
      ((((¬Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom1333 chi) ∨
      (Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom0600 chi)) ∨
      ((Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom0609 chi) ∨
      (Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom0618 chi))) ∨
      (((Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom0663 chi) ∨
      (Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom1334 chi)) ∨
      ((¬Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom1334 chi) ∨
      (Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom0601 chi))))) ∨
      (((((Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom0602 chi) ∨
      (Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom0619 chi)) ∨
      ((Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom0664 chi) ∨
      (Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom1335 chi))) ∨
      (((¬Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom1335 chi) ∨
      (Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom0601 chi)) ∨
      ((Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom0603 chi) ∨
      (Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom0620 chi)))) ∨
      ((((Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom0665 chi) ∨
      (Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom1336 chi)) ∨
      ((¬Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom1336 chi) ∨
      (Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom0601 chi))) ∨
      (((Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom0604 chi) ∨
      (Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom0621 chi)) ∨
      ((Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom0666 chi) ∨
      (Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom1337 chi)))))))))) := by
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
                exact fin15Anchored_clause17668 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17669 chi hbad
                ·
                  exact fin15Anchored_clause17670 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17671 chi hbad
                ·
                  exact fin15Anchored_clause17672 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17673 chi hbad
                ·
                  exact fin15Anchored_clause17674 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17675 chi hbad
                ·
                  exact fin15Anchored_clause17676 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17677 chi hbad
                ·
                  exact fin15Anchored_clause17678 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17679 chi hbad
                ·
                  exact fin15Anchored_clause17680 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17681 chi hbad
                ·
                  exact fin15Anchored_clause17682 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17683 chi hbad
                ·
                  exact fin15Anchored_clause17684 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17685 chi hbad
                ·
                  exact fin15Anchored_clause17686 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17687 chi hbad
                ·
                  exact fin15Anchored_clause17688 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17689 chi hbad
                ·
                  exact fin15Anchored_clause17690 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17691 chi hbad
                ·
                  exact fin15Anchored_clause17692 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17693 chi hbad
                ·
                  exact fin15Anchored_clause17694 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17695 chi hbad
                ·
                  exact fin15Anchored_clause17696 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17697 chi hbad
                ·
                  exact fin15Anchored_clause17698 chi hbad
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
                  exact fin15Anchored_clause17699 chi hbad
                ·
                  exact fin15Anchored_clause17700 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17701 chi hbad
                ·
                  exact fin15Anchored_clause17702 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17703 chi hbad
                ·
                  exact fin15Anchored_clause17704 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17705 chi hbad
                ·
                  exact fin15Anchored_clause17706 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17707 chi hbad
                ·
                  exact fin15Anchored_clause17708 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17709 chi hbad
                ·
                  exact fin15Anchored_clause17710 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17711 chi hbad
                ·
                  exact fin15Anchored_clause17712 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17713 chi hbad
                ·
                  exact fin15Anchored_clause17714 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17715 chi hbad
                ·
                  exact fin15Anchored_clause17716 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17717 chi hbad
                ·
                  exact fin15Anchored_clause17718 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17719 chi hbad
                ·
                  exact fin15Anchored_clause17720 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17721 chi hbad
                ·
                  exact fin15Anchored_clause17722 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17723 chi hbad
                ·
                  exact fin15Anchored_clause17724 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17725 chi hbad
                ·
                  exact fin15Anchored_clause17726 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17727 chi hbad
                ·
                  exact fin15Anchored_clause17728 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17729 chi hbad
                ·
                  exact fin15Anchored_clause17730 chi hbad
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
                exact fin15Anchored_clause17731 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17732 chi hbad
                ·
                  exact fin15Anchored_clause17733 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17734 chi hbad
                ·
                  exact fin15Anchored_clause17735 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17736 chi hbad
                ·
                  exact fin15Anchored_clause17737 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17738 chi hbad
                ·
                  exact fin15Anchored_clause17739 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17740 chi hbad
                ·
                  exact fin15Anchored_clause17741 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17742 chi hbad
                ·
                  exact fin15Anchored_clause17743 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17744 chi hbad
                ·
                  exact fin15Anchored_clause17745 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17746 chi hbad
                ·
                  exact fin15Anchored_clause17747 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17748 chi hbad
                ·
                  exact fin15Anchored_clause17749 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17750 chi hbad
                ·
                  exact fin15Anchored_clause17751 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17752 chi hbad
                ·
                  exact fin15Anchored_clause17753 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17754 chi hbad
                ·
                  exact fin15Anchored_clause17755 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17756 chi hbad
                ·
                  exact fin15Anchored_clause17757 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17758 chi hbad
                ·
                  exact fin15Anchored_clause17759 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17760 chi hbad
                ·
                  exact fin15Anchored_clause17761 chi hbad
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
                  exact fin15Anchored_clause17762 chi hbad
                ·
                  exact fin15Anchored_clause17763 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17764 chi hbad
                ·
                  exact fin15Anchored_clause17765 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17766 chi hbad
                ·
                  exact fin15Anchored_clause17767 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17768 chi hbad
                ·
                  exact fin15Anchored_clause17769 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17770 chi hbad
                ·
                  exact fin15Anchored_clause17771 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17772 chi hbad
                ·
                  exact fin15Anchored_clause17773 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17774 chi hbad
                ·
                  exact fin15Anchored_clause17775 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17776 chi hbad
                ·
                  exact fin15Anchored_clause17777 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17778 chi hbad
                ·
                  exact fin15Anchored_clause17779 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17780 chi hbad
                ·
                  exact fin15Anchored_clause17781 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17782 chi hbad
                ·
                  exact fin15Anchored_clause17783 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17784 chi hbad
                ·
                  exact fin15Anchored_clause17785 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17786 chi hbad
                ·
                  exact fin15Anchored_clause17787 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17788 chi hbad
                ·
                  exact fin15Anchored_clause17789 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17790 chi hbad
                ·
                  exact fin15Anchored_clause17791 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17792 chi hbad
                ·
                  exact fin15Anchored_clause17793 chi hbad
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
                exact fin15Anchored_clause17794 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17795 chi hbad
                ·
                  exact fin15Anchored_clause17796 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17797 chi hbad
                ·
                  exact fin15Anchored_clause17798 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17799 chi hbad
                ·
                  exact fin15Anchored_clause17800 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17801 chi hbad
                ·
                  exact fin15Anchored_clause17802 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17803 chi hbad
                ·
                  exact fin15Anchored_clause17804 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17805 chi hbad
                ·
                  exact fin15Anchored_clause17806 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17807 chi hbad
                ·
                  exact fin15Anchored_clause17808 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17809 chi hbad
                ·
                  exact fin15Anchored_clause17810 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17811 chi hbad
                ·
                  exact fin15Anchored_clause17812 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17813 chi hbad
                ·
                  exact fin15Anchored_clause17814 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17815 chi hbad
                ·
                  exact fin15Anchored_clause17816 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17817 chi hbad
                ·
                  exact fin15Anchored_clause17818 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17819 chi hbad
                ·
                  exact fin15Anchored_clause17820 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17821 chi hbad
                ·
                  exact fin15Anchored_clause17822 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17823 chi hbad
                ·
                  exact fin15Anchored_clause17824 chi hbad
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
                  exact fin15Anchored_clause17825 chi hbad
                ·
                  exact fin15Anchored_clause17826 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17827 chi hbad
                ·
                  exact fin15Anchored_clause17828 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17829 chi hbad
                ·
                  exact fin15Anchored_clause17830 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17831 chi hbad
                ·
                  exact fin15Anchored_clause17832 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17833 chi hbad
                ·
                  exact fin15Anchored_clause17834 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17835 chi hbad
                ·
                  exact fin15Anchored_clause17836 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17837 chi hbad
                ·
                  exact fin15Anchored_clause17838 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17839 chi hbad
                ·
                  exact fin15Anchored_clause17840 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17841 chi hbad
                ·
                  exact fin15Anchored_clause17842 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17843 chi hbad
                ·
                  exact fin15Anchored_clause17844 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17845 chi hbad
                ·
                  exact fin15Anchored_clause17846 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17847 chi hbad
                ·
                  exact fin15Anchored_clause17848 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17849 chi hbad
                ·
                  exact fin15Anchored_clause17850 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17851 chi hbad
                ·
                  exact fin15Anchored_clause17852 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17853 chi hbad
                ·
                  exact fin15Anchored_clause17854 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17855 chi hbad
                ·
                  exact fin15Anchored_clause17856 chi hbad
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
                exact fin15Anchored_clause17857 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17858 chi hbad
                ·
                  exact fin15Anchored_clause17859 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17860 chi hbad
                ·
                  exact fin15Anchored_clause17861 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17862 chi hbad
                ·
                  exact fin15Anchored_clause17863 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17864 chi hbad
                ·
                  exact fin15Anchored_clause17865 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17866 chi hbad
                ·
                  exact fin15Anchored_clause17867 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17868 chi hbad
                ·
                  exact fin15Anchored_clause17869 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17870 chi hbad
                ·
                  exact fin15Anchored_clause17871 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17872 chi hbad
                ·
                  exact fin15Anchored_clause17873 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17874 chi hbad
                ·
                  exact fin15Anchored_clause17875 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17876 chi hbad
                ·
                  exact fin15Anchored_clause17877 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17878 chi hbad
                ·
                  exact fin15Anchored_clause17879 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17880 chi hbad
                ·
                  exact fin15Anchored_clause17881 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17882 chi hbad
                ·
                  exact fin15Anchored_clause17883 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17884 chi hbad
                ·
                  exact fin15Anchored_clause17885 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17886 chi hbad
                ·
                  exact fin15Anchored_clause17887 chi hbad
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
                  exact fin15Anchored_clause17888 chi hbad
                ·
                  exact fin15Anchored_clause17889 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17890 chi hbad
                ·
                  exact fin15Anchored_clause17891 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17892 chi hbad
                ·
                  exact fin15Anchored_clause17893 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17894 chi hbad
                ·
                  exact fin15Anchored_clause17895 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17896 chi hbad
                ·
                  exact fin15Anchored_clause17897 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17898 chi hbad
                ·
                  exact fin15Anchored_clause17899 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17900 chi hbad
                ·
                  exact fin15Anchored_clause17901 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17902 chi hbad
                ·
                  exact fin15Anchored_clause17903 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17904 chi hbad
                ·
                  exact fin15Anchored_clause17905 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17906 chi hbad
                ·
                  exact fin15Anchored_clause17907 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17908 chi hbad
                ·
                  exact fin15Anchored_clause17909 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17910 chi hbad
                ·
                  exact fin15Anchored_clause17911 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17912 chi hbad
                ·
                  exact fin15Anchored_clause17913 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17914 chi hbad
                ·
                  exact fin15Anchored_clause17915 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17916 chi hbad
                ·
                  exact fin15Anchored_clause17917 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause17918 chi hbad
                ·
                  exact fin15Anchored_clause17919 chi hbad

end ErdosSzekeres

end
