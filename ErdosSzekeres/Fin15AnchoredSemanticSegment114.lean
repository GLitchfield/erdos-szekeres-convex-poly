module

public import ErdosSzekeres.Fin15AnchoredClauseChunk224
public import ErdosSzekeres.Fin15AnchoredClauseChunk225
public import ErdosSzekeres.Fin15AnchoredClauseChunk226

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 114. -/

theorem fin15Anchored_rejectSemanticSegment114
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom3740 chi) ∨
      ((Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom3742 chi) ∨
      (Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom3743 chi))) ∨
      (((Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom3744 chi) ∨
      (Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom3751 chi)) ∨
      ((Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom3753 chi) ∨
      (Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom3754 chi)))) ∨
      ((((Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom3755 chi) ∨
      (Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom3757 chi)) ∨
      ((Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom3758 chi) ∨
      (Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom3759 chi))) ∨
      (((Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom3763 chi) ∨
      (Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom3764 chi)) ∨
      ((Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom3765 chi) ∨
      (Fin15AnchoredAtom2179 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2187 chi ∧
      Fin15AnchoredAtom2272 chi ∧
      Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom3767 chi))))) ∨
      (((((Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom3772 chi) ∨
      (Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom3774 chi)) ∨
      ((Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom3775 chi) ∨
      (Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom3776 chi))) ∨
      (((Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom3778 chi) ∨
      (Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom3779 chi)) ∨
      ((Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom3780 chi) ∨
      (Fin15AnchoredAtom2182 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2201 chi ∧
      Fin15AnchoredAtom2286 chi ∧
      Fin15AnchoredAtom2571 chi ∧
      Fin15AnchoredAtom3781 chi)))) ∨
      ((((Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom3784 chi) ∨
      (Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom3785 chi)) ∨
      ((Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom3786 chi) ∨
      (Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom3803 chi))) ∨
      (((Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom3804 chi) ∨
      (Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom3805 chi)) ∨
      ((Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom3809 chi) ∨
      (Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom3810 chi)))))) ∨
      ((((((Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom3811 chi) ∨
      (Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom3815 chi)) ∨
      ((Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom3816 chi) ∨
      (Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom3817 chi))) ∨
      (((Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom3821 chi) ∨
      (Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom3823 chi)) ∨
      ((Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom3824 chi) ∨
      (Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom3826 chi)))) ∨
      ((((Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom3827 chi) ∨
      (Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom3828 chi)) ∨
      ((Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom3835 chi) ∨
      (Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom3837 chi))) ∨
      (((Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom3838 chi) ∨
      (Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom3839 chi)) ∨
      ((Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom3841 chi) ∨
      (Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom3842 chi))))) ∨
      (((((Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom3843 chi) ∨
      (Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom3847 chi)) ∨
      ((Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom3848 chi) ∨
      (Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom3849 chi))) ∨
      (((Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom3856 chi) ∨
      (Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom3858 chi)) ∨
      ((Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom3859 chi) ∨
      (Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom3860 chi)))) ∨
      ((((Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom3862 chi) ∨
      (Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom3863 chi)) ∨
      ((Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom3864 chi) ∨
      (Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom3868 chi))) ∨
      (((Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom3869 chi) ∨
      (Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom3870 chi)) ∨
      ((Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom3887 chi) ∨
      (Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom3888 chi))))))) ∨
      ((((((Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom3889 chi) ∨
      ((Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom3893 chi) ∨
      (Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom3894 chi))) ∨
      (((Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom3895 chi) ∨
      (Fin15AnchoredAtom2233 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2238 chi ∧
      Fin15AnchoredAtom2318 chi ∧
      Fin15AnchoredAtom2687 chi ∧
      Fin15AnchoredAtom3897 chi)) ∨
      ((Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom3899 chi) ∨
      (Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom3900 chi)))) ∨
      ((((Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom3901 chi) ∨
      (Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom3905 chi)) ∨
      ((Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom3912 chi) ∨
      (Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom3914 chi))) ∨
      (((Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom3915 chi) ∨
      (Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom3916 chi)) ∨
      ((Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom3918 chi) ∨
      (Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom3919 chi))))) ∨
      (((((Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom3920 chi) ∨
      (Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom3924 chi)) ∨
      ((Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom3925 chi) ∨
      (Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom3926 chi))) ∨
      (((Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom3943 chi) ∨
      (Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom3944 chi)) ∨
      ((Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom3945 chi) ∨
      (Fin15AnchoredAtom2257 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2267 chi ∧
      Fin15AnchoredAtom2313 chi ∧
      Fin15AnchoredAtom2738 chi ∧
      Fin15AnchoredAtom3948 chi)))) ∨
      ((((Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom3949 chi) ∨
      (Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom3950 chi)) ∨
      ((Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom3951 chi) ∨
      (Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom3955 chi))) ∨
      (((Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom3956 chi) ∨
      (Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom3957 chi)) ∨
      ((Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom3961 chi) ∨
      (Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom3978 chi)))))) ∨
      ((((((Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom3979 chi) ∨
      (Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom3980 chi)) ∨
      ((Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom3984 chi) ∨
      (Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom3985 chi))) ∨
      (((Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom3986 chi) ∨
      (Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom3990 chi)) ∨
      ((Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom3991 chi) ∨
      (Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom3992 chi)))) ∨
      ((((Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom3996 chi) ∨
      (Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4020 chi)) ∨
      ((Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4021 chi) ∨
      (Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4022 chi))) ∨
      (((Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4026 chi) ∨
      (Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4030 chi)) ∨
      ((Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom4032 chi) ∨
      (Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2373 chi ∧
      Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom4033 chi))))) ∨
      (((((Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom4034 chi) ∨
      (Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom4035 chi)) ∨
      ((Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2332 chi ∧
      Fin15AnchoredAtom2340 chi ∧
      Fin15AnchoredAtom2376 chi ∧
      Fin15AnchoredAtom2496 chi ∧
      Fin15AnchoredAtom4036 chi) ∨
      (Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom4037 chi))) ∨
      (((Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom4038 chi) ∨
      (Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom4039 chi)) ∨
      ((Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom4040 chi) ∨
      (Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom4041 chi)))) ∨
      ((((Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom4042 chi) ∨
      (Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom4044 chi)) ∨
      ((Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom4045 chi) ∨
      (Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom4046 chi))) ∨
      (((Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom4047 chi) ∨
      (Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom4048 chi)) ∨
      ((Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom4050 chi) ∨
      (Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2391 chi ∧
      Fin15AnchoredAtom2511 chi ∧
      Fin15AnchoredAtom4051 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom4052 chi) ∨
      ((Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom4053 chi) ∨
      (Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2332 chi ∧
      Fin15AnchoredAtom2358 chi ∧
      Fin15AnchoredAtom2394 chi ∧
      Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom4054 chi))) ∨
      (((Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom4055 chi) ∨
      (Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom4056 chi)) ∨
      ((Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom4057 chi) ∨
      (Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom4059 chi)))) ∨
      ((((Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom4060 chi) ∨
      (Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom4061 chi)) ∨
      ((Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom4065 chi) ∨
      (Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom4066 chi))) ∨
      (((Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom4067 chi) ∨
      (Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom4068 chi)) ∨
      ((Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom4069 chi) ∨
      (Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom4070 chi))))) ∨
      (((((Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom4072 chi) ∨
      (Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom4073 chi)) ∨
      ((Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom4074 chi) ∨
      (Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom4075 chi))) ∨
      (((Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom4076 chi) ∨
      (Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom4078 chi)) ∨
      ((Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom4079 chi) ∨
      (Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom4080 chi)))) ∨
      ((((Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom4081 chi) ∨
      (Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom4083 chi)) ∨
      ((Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom4084 chi) ∨
      (Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom4085 chi))) ∨
      (((Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom4087 chi) ∨
      (Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom4088 chi)) ∨
      ((Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom4089 chi) ∨
      (Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom4093 chi)))))) ∨
      ((((((Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom4094 chi) ∨
      (Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom4095 chi)) ∨
      ((Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom4096 chi) ∨
      (Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom4097 chi))) ∨
      (((Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom4099 chi) ∨
      (Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2560 chi ∧
      Fin15AnchoredAtom4100 chi)) ∨
      ((Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2561 chi ∧
      Fin15AnchoredAtom4101 chi) ∨
      (Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom4102 chi)))) ∨
      ((((Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom4104 chi) ∨
      (Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom4105 chi)) ∨
      ((Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom4106 chi) ∨
      (Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom4108 chi))) ∨
      (((Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom4109 chi) ∨
      (Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom4110 chi)) ∨
      ((Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom4114 chi) ∨
      (Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom4115 chi))))) ∨
      (((((Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom4116 chi) ∨
      (Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom4117 chi)) ∨
      ((Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom4119 chi) ∨
      (Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom2580 chi ∧
      Fin15AnchoredAtom4120 chi))) ∨
      (((Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom4121 chi) ∨
      (Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom4123 chi)) ∨
      ((Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2584 chi ∧
      Fin15AnchoredAtom4124 chi) ∨
      (Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom4125 chi)))) ∨
      ((((Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom4129 chi) ∨
      (Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom4130 chi)) ∨
      ((Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom4131 chi) ∨
      (Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom4133 chi))) ∨
      (((Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom4134 chi) ∨
      (Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom4135 chi)) ∨
      ((Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom4139 chi) ∨
      (Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom4140 chi))))))) ∨
      ((((((Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom4141 chi) ∨
      ((Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom4145 chi) ∨
      (Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom4146 chi))) ∨
      (((Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom4147 chi) ∨
      (Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom4151 chi)) ∨
      ((Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom4153 chi) ∨
      (Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom4154 chi)))) ∨
      ((((Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom4156 chi) ∨
      (Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom4157 chi)) ∨
      ((Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom4158 chi) ∨
      (Fin15AnchoredAtom2373 chi ∧
      Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2619 chi ∧
      Fin15AnchoredAtom4159 chi))) ∨
      (((Fin15AnchoredAtom2373 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom4164 chi) ∨
      (Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom4165 chi)) ∨
      ((Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom4167 chi) ∨
      (Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom4168 chi))))) ∨
      (((((Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom4169 chi) ∨
      (Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom4171 chi)) ∨
      ((Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom4172 chi) ∨
      (Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom4173 chi))) ∨
      (((Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom4177 chi) ∨
      (Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom4178 chi)) ∨
      ((Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom4179 chi) ∨
      (Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom4180 chi)))) ∨
      ((((Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2641 chi ∧
      Fin15AnchoredAtom4181 chi) ∨
      (Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2643 chi ∧
      Fin15AnchoredAtom4183 chi)) ∨
      ((Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2391 chi ∧
      Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2644 chi ∧
      Fin15AnchoredAtom4184 chi) ∨
      (Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom4185 chi))) ∨
      (((Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom4186 chi) ∨
      (Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom4188 chi)) ∨
      ((Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom4189 chi) ∨
      (Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom4190 chi)))))) ∨
      ((((((Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom4192 chi) ∨
      (Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom4193 chi)) ∨
      ((Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom4194 chi) ∨
      (Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom4198 chi))) ∨
      (((Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom4199 chi) ∨
      (Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom4200 chi)) ∨
      ((Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2661 chi ∧
      Fin15AnchoredAtom4201 chi) ∨
      (Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom4203 chi)))) ∨
      ((((Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom4205 chi) ∨
      (Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2667 chi ∧
      Fin15AnchoredAtom4207 chi)) ∨
      ((Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom2391 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2668 chi ∧
      Fin15AnchoredAtom4208 chi) ∨
      (Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom4214 chi))) ∨
      (((Fin15AnchoredAtom2391 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom4215 chi) ∨
      (Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom4217 chi)) ∨
      ((Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom4218 chi) ∨
      (Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom4219 chi))))) ∨
      (((((Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom4223 chi) ∨
      (Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom4224 chi)) ∨
      ((Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom4225 chi) ∨
      (Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom4229 chi))) ∨
      (((Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom4230 chi) ∨
      (Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom4231 chi)) ∨
      ((Fin15AnchoredAtom2403 chi ∧
      Fin15AnchoredAtom2404 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2490 chi ∧
      Fin15AnchoredAtom2694 chi ∧
      Fin15AnchoredAtom4234 chi) ∨
      (Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom4235 chi)))) ∨
      ((((Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom4236 chi) ∨
      (Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2700 chi ∧
      Fin15AnchoredAtom4240 chi)) ∨
      ((Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2701 chi ∧
      Fin15AnchoredAtom4241 chi) ∨
      (Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom4242 chi))) ∨
      (((Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom4244 chi) ∨
      (Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom4245 chi)) ∨
      ((Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom4246 chi) ∨
      (Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom4248 chi)))))))))) := by
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
                exact fin15Anchored_clause28774 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28775 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28776 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28777 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28778 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28779 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28780 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28781 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28782 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28783 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28784 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28785 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28786 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28787 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28788 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28789 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28790 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28791 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28792 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28793 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28794 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28795 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28796 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28797 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28798 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28799 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28800 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28801 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28802 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28803 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28804 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28805 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28806 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28807 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28808 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28809 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28810 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28811 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28812 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28813 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28814 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28815 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28816 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28817 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28818 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28819 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28820 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28821 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28822 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28823 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28824 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28825 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28826 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28827 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28828 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28829 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28830 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28831 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28832 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28833 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28834 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28835 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28836 chi hnoStrong hbad
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
                exact fin15Anchored_clause28837 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28838 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28839 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28840 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28841 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28842 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28843 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28844 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28845 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28846 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28847 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28848 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28849 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28850 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28851 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28852 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28853 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28854 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28855 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28856 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28857 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28858 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28859 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28860 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28861 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28862 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28863 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28864 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28865 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28866 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28867 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28868 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28869 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28870 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28871 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28872 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28873 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28874 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28875 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28876 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28877 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28878 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28879 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28880 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28881 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28882 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28883 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28884 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28885 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28886 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28887 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28888 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28889 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28890 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28891 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28892 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28893 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28894 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28895 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28896 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28897 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28898 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28899 chi hnoStrong hbad
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
                exact fin15Anchored_clause28900 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28901 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28902 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28903 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28904 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28905 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28906 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28907 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28908 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28909 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28910 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28911 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28912 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28913 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28914 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28915 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28916 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28917 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28918 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28919 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28920 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28921 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28922 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28923 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28924 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28925 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28926 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28927 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28928 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28929 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28930 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28931 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28932 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28933 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28934 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28935 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28936 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28937 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28938 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28939 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28940 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28941 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28942 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28943 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28944 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28945 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28946 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28947 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28948 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28949 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28950 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28951 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28952 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28953 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28954 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28955 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28956 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28957 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28958 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28959 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28960 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28961 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28962 chi hnoStrong hbad
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
                exact fin15Anchored_clause28963 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28964 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28965 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28966 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28967 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28968 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28969 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28970 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28971 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28972 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28973 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28974 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28975 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28976 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28977 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28978 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28979 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28980 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28981 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28982 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28983 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28984 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28985 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28986 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28987 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28988 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28989 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28990 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28991 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28992 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28993 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28994 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28995 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28996 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28997 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28998 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28999 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29000 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29001 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29002 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29003 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29004 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29005 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29006 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29007 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29008 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29009 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29010 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29011 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29012 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29013 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29014 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29015 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29016 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29017 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29018 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29019 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29020 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29021 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29022 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29023 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29024 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29025 chi hnoStrong hbad

end ErdosSzekeres

end
