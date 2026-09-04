module

public import ErdosSzekeres.Fin15AnchoredClauseChunk222
public import ErdosSzekeres.Fin15AnchoredClauseChunk223
public import ErdosSzekeres.Fin15AnchoredClauseChunk224

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 113. -/

theorem fin15Anchored_rejectSemanticSegment113
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom3284 chi) ∨
      ((Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom3285 chi) ∨
      (Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom3289 chi))) ∨
      (((Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom3290 chi) ∨
      (Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom3291 chi)) ∨
      ((Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom3292 chi) ∨
      (Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom1969 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom3298 chi)))) ∨
      ((((Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom1970 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2584 chi ∧
      Fin15AnchoredAtom3299 chi) ∨
      (Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2080 chi ∧
      Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom3300 chi)) ∨
      ((Fin15AnchoredAtom1969 chi ∧
      Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom3305 chi) ∨
      (Fin15AnchoredAtom1970 chi ∧
      Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom3306 chi))) ∨
      (((Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom3308 chi) ∨
      (Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom3309 chi)) ∨
      ((Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom3310 chi) ∨
      (Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom3314 chi))))) ∨
      (((((Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom3315 chi) ∨
      (Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom3316 chi)) ∨
      ((Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom3320 chi) ∨
      (Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom3321 chi))) ∨
      (((Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom3322 chi) ∨
      (Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom3326 chi)) ∨
      ((Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom3328 chi) ∨
      (Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom3329 chi)))) ∨
      ((((Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom3331 chi) ∨
      (Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom3332 chi)) ∨
      ((Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom3333 chi) ∨
      (Fin15AnchoredAtom1988 chi ∧
      Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2619 chi ∧
      Fin15AnchoredAtom3334 chi))) ∨
      (((Fin15AnchoredAtom1988 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom2003 chi ∧
      Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom2620 chi ∧
      Fin15AnchoredAtom3335 chi) ∨
      (Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom3340 chi)) ∨
      ((Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom3342 chi) ∨
      (Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom3343 chi)))))) ∨
      ((((((Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom3344 chi) ∨
      (Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom3346 chi)) ∨
      ((Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom3347 chi) ∨
      (Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom3348 chi))) ∨
      (((Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom3352 chi) ∨
      (Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom3353 chi)) ∨
      ((Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom3354 chi) ∨
      (Fin15AnchoredAtom1995 chi ∧
      Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom3355 chi)))) ∨
      ((((Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom3361 chi) ∨
      (Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom3363 chi)) ∨
      ((Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom3364 chi) ∨
      (Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom3365 chi))) ∨
      (((Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom3367 chi) ∨
      (Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom3368 chi)) ∨
      ((Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom3369 chi) ∨
      (Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom3373 chi))))) ∨
      (((((Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom3374 chi) ∨
      (Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom3375 chi)) ∨
      ((Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom2006 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2664 chi ∧
      Fin15AnchoredAtom3379 chi) ∨
      (Fin15AnchoredAtom2003 chi ∧
      Fin15AnchoredAtom2006 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2668 chi ∧
      Fin15AnchoredAtom3383 chi))) ∨
      (((Fin15AnchoredAtom2005 chi ∧
      Fin15AnchoredAtom2006 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom3388 chi) ∨
      (Fin15AnchoredAtom2005 chi ∧
      Fin15AnchoredAtom2007 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom3389 chi)) ∨
      ((Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom3392 chi) ∨
      (Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom3393 chi)))) ∨
      ((((Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom3394 chi) ∨
      (Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom3398 chi)) ∨
      ((Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom3399 chi) ∨
      (Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom3400 chi))) ∨
      (((Fin15AnchoredAtom2013 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2018 chi ∧
      Fin15AnchoredAtom2098 chi ∧
      Fin15AnchoredAtom2687 chi ∧
      Fin15AnchoredAtom3402 chi) ∨
      (Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom3404 chi)) ∨
      ((Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom3405 chi) ∨
      (Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom3406 chi))))))) ∨
      ((((((Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom3410 chi) ∨
      ((Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom3417 chi) ∨
      (Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom3419 chi))) ∨
      (((Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom3420 chi) ∨
      (Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom3421 chi)) ∨
      ((Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom3423 chi) ∨
      (Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom3424 chi)))) ∨
      ((((Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom3425 chi) ∨
      (Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom3429 chi)) ∨
      ((Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom3430 chi) ∨
      (Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom3431 chi))) ∨
      (((Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom3432 chi) ∨
      (Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2033 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom3434 chi)) ∨
      ((Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2034 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom3435 chi) ∨
      (Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom2034 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom3439 chi))))) ∨
      (((((Fin15AnchoredAtom2033 chi ∧
      Fin15AnchoredAtom2034 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom3444 chi) ∨
      (Fin15AnchoredAtom2033 chi ∧
      Fin15AnchoredAtom2035 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom3445 chi)) ∨
      ((Fin15AnchoredAtom2034 chi ∧
      Fin15AnchoredAtom2035 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom3446 chi) ∨
      (Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom3448 chi))) ∨
      (((Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom3449 chi) ∨
      (Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom3450 chi)) ∨
      ((Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom3454 chi) ∨
      (Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom3455 chi)))) ∨
      ((((Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom3456 chi) ∨
      (Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom3460 chi)) ∨
      ((Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom3461 chi) ∨
      (Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom3462 chi))) ∨
      (((Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom3466 chi) ∨
      (Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2052 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom3467 chi)) ∨
      ((Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2054 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom3469 chi) ∨
      (Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2055 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom3470 chi)))))) ∨
      ((((((Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2056 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2076 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom3471 chi) ∨
      (Fin15AnchoredAtom2052 chi ∧
      Fin15AnchoredAtom2054 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom3473 chi)) ∨
      ((Fin15AnchoredAtom2054 chi ∧
      Fin15AnchoredAtom2056 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom3480 chi) ∨
      (Fin15AnchoredAtom2055 chi ∧
      Fin15AnchoredAtom2056 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom3481 chi))) ∨
      (((Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom3483 chi) ∨
      (Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom3484 chi)) ∨
      ((Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom3485 chi) ∨
      (Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom3489 chi)))) ∨
      ((((Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom3490 chi) ∨
      (Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom3491 chi)) ∨
      ((Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom3495 chi) ∨
      (Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom3496 chi))) ∨
      (((Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom3497 chi) ∨
      (Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom3501 chi)) ∨
      ((Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom3503 chi) ∨
      (Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom3504 chi))))) ∨
      (((((Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom2076 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom3510 chi) ∨
      (Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2076 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom3511 chi)) ∨
      ((Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom3515 chi) ∨
      (Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2080 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom3516 chi))) ∨
      (((Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2080 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom3517 chi) ∨
      (Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom3521 chi)) ∨
      ((Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom3525 chi) ∨
      (Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom3526 chi)))) ∨
      ((((Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom3527 chi) ∨
      (Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom3531 chi)) ∨
      ((Fin15AnchoredAtom2097 chi ∧
      Fin15AnchoredAtom2098 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2103 chi ∧
      Fin15AnchoredAtom2817 chi ∧
      Fin15AnchoredAtom3532 chi) ∨
      (Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom3535 chi))) ∨
      (((Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom3537 chi) ∨
      (Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom3538 chi)) ∨
      ((Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom3540 chi) ∨
      (Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom3541 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2113 chi ∧
      Fin15AnchoredAtom2122 chi ∧
      Fin15AnchoredAtom2167 chi ∧
      Fin15AnchoredAtom2332 chi ∧
      Fin15AnchoredAtom3542 chi) ∨
      ((Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom3543 chi) ∨
      (Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom3544 chi))) ∨
      (((Fin15AnchoredAtom2107 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom3545 chi) ∨
      (Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom3546 chi)) ∨
      ((Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom3548 chi) ∨
      (Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom3549 chi)))) ∨
      ((((Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom3551 chi) ∨
      (Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom3552 chi)) ∨
      ((Fin15AnchoredAtom2108 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom3553 chi) ∨
      (Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2110 chi ∧
      Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom2179 chi ∧
      Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom3554 chi))) ∨
      (((Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom3555 chi) ∨
      (Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom3556 chi)) ∨
      ((Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2113 chi ∧
      Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2182 chi ∧
      Fin15AnchoredAtom2347 chi ∧
      Fin15AnchoredAtom3557 chi) ∨
      (Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom3558 chi))))) ∨
      (((((Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom3559 chi) ∨
      (Fin15AnchoredAtom2109 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom3560 chi)) ∨
      ((Fin15AnchoredAtom2110 chi ∧
      Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2141 chi ∧
      Fin15AnchoredAtom2186 chi ∧
      Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom3561 chi) ∨
      (Fin15AnchoredAtom2110 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2187 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom3562 chi))) ∨
      (((Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom3567 chi) ∨
      (Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom3569 chi)) ∨
      ((Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom3570 chi) ∨
      (Fin15AnchoredAtom2111 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom3571 chi)))) ∨
      ((((Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom3573 chi) ∨
      (Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom3574 chi)) ∨
      ((Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom3575 chi) ∨
      (Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom3579 chi))) ∨
      (((Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom3580 chi) ∨
      (Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom3581 chi)) ∨
      ((Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom3582 chi) ∨
      (Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom3584 chi)))))) ∨
      ((((((Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom3585 chi) ∨
      (Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom3587 chi)) ∨
      ((Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom3588 chi) ∨
      (Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom3589 chi))) ∨
      (((Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom2215 chi ∧
      Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom3590 chi) ∨
      (Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom3591 chi)) ∨
      ((Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom3592 chi) ∨
      (Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2122 chi ∧
      Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2218 chi ∧
      Fin15AnchoredAtom2383 chi ∧
      Fin15AnchoredAtom3593 chi)))) ∨
      ((((Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom3594 chi) ∨
      (Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom3595 chi)) ∨
      ((Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom3596 chi) ∨
      (Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2141 chi ∧
      Fin15AnchoredAtom2222 chi ∧
      Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom3597 chi))) ∨
      (((Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2223 chi ∧
      Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom3598 chi) ∨
      (Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2146 chi ∧
      Fin15AnchoredAtom2227 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom3602 chi)) ∨
      ((Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom3603 chi) ∨
      (Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom3605 chi))))) ∨
      (((((Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom3606 chi) ∨
      (Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom3607 chi)) ∨
      ((Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2122 chi ∧
      Fin15AnchoredAtom2152 chi ∧
      Fin15AnchoredAtom2233 chi ∧
      Fin15AnchoredAtom2398 chi ∧
      Fin15AnchoredAtom3608 chi) ∨
      (Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom3609 chi))) ∨
      (((Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom3610 chi) ∨
      (Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom3611 chi)) ∨
      ((Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom3615 chi) ∨
      (Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom3616 chi)))) ∨
      ((((Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom3617 chi) ∨
      (Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom3619 chi)) ∨
      ((Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom3620 chi) ∨
      (Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2130 chi ∧
      Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2246 chi ∧
      Fin15AnchoredAtom2411 chi ∧
      Fin15AnchoredAtom3621 chi))) ∨
      (((Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom3622 chi) ∨
      (Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom3623 chi)) ∨
      ((Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom3624 chi) ∨
      (Fin15AnchoredAtom2127 chi ∧
      Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2141 chi ∧
      Fin15AnchoredAtom2250 chi ∧
      Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom3625 chi))))))) ∨
      ((((((Fin15AnchoredAtom2127 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2251 chi ∧
      Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom3626 chi) ∨
      ((Fin15AnchoredAtom2127 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2144 chi ∧
      Fin15AnchoredAtom2253 chi ∧
      Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom3628 chi) ∨
      (Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom3631 chi))) ∨
      (((Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom3633 chi) ∨
      (Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom3634 chi)) ∨
      ((Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom3635 chi) ∨
      (Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2130 chi ∧
      Fin15AnchoredAtom2152 chi ∧
      Fin15AnchoredAtom2261 chi ∧
      Fin15AnchoredAtom2426 chi ∧
      Fin15AnchoredAtom3636 chi)))) ∨
      ((((Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom3637 chi) ∨
      (Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom3638 chi)) ∨
      ((Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom3639 chi) ∨
      (Fin15AnchoredAtom2130 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2157 chi ∧
      Fin15AnchoredAtom2266 chi ∧
      Fin15AnchoredAtom2431 chi ∧
      Fin15AnchoredAtom3641 chi))) ∨
      (((Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom3643 chi) ∨
      (Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom3644 chi)) ∨
      ((Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom3645 chi) ∨
      (Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2272 chi ∧
      Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom3647 chi))))) ∨
      (((((Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2146 chi ∧
      Fin15AnchoredAtom2276 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom3651 chi) ∨
      (Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom3652 chi)) ∨
      ((Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2148 chi ∧
      Fin15AnchoredAtom2278 chi ∧
      Fin15AnchoredAtom2443 chi ∧
      Fin15AnchoredAtom3653 chi) ∨
      (Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom3654 chi))) ∨
      (((Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom3655 chi) ∨
      (Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom3656 chi)) ∨
      ((Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2152 chi ∧
      Fin15AnchoredAtom2282 chi ∧
      Fin15AnchoredAtom2447 chi ∧
      Fin15AnchoredAtom3657 chi) ∨
      (Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom3658 chi)))) ∨
      ((((Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom3659 chi) ∨
      (Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom3660 chi)) ∨
      ((Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2158 chi ∧
      Fin15AnchoredAtom2288 chi ∧
      Fin15AnchoredAtom2453 chi ∧
      Fin15AnchoredAtom3663 chi) ∨
      (Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom3664 chi))) ∨
      (((Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom3665 chi) ∨
      (Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom3666 chi)) ∨
      ((Fin15AnchoredAtom2141 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2292 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom3667 chi) ∨
      (Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom3683 chi)))))) ∨
      ((((((Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom3684 chi) ∨
      (Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom3685 chi)) ∨
      ((Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom3689 chi) ∨
      (Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom3690 chi))) ∨
      (((Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom3691 chi) ∨
      (Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom3695 chi)) ∨
      ((Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom3696 chi) ∨
      (Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom3697 chi)))) ∨
      ((((Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom3701 chi) ∨
      (Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom3702 chi)) ∨
      ((Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom3704 chi) ∨
      (Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom3705 chi))) ∨
      (((Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom3707 chi) ∨
      (Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom3708 chi)) ∨
      ((Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom3709 chi) ∨
      (Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom3711 chi))))) ∨
      (((((Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom3712 chi) ∨
      (Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom3714 chi)) ∨
      ((Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom3715 chi) ∨
      (Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom3716 chi))) ∨
      (((Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom3723 chi) ∨
      (Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom3725 chi)) ∨
      ((Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom3726 chi) ∨
      (Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom3727 chi)))) ∨
      ((((Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom3729 chi) ∨
      (Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom3730 chi)) ∨
      ((Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom3731 chi) ∨
      (Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom3735 chi))) ∨
      (((Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom3736 chi) ∨
      (Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom3737 chi)) ∨
      ((Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2172 chi ∧
      Fin15AnchoredAtom2179 chi ∧
      Fin15AnchoredAtom2243 chi ∧
      Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom3738 chi) ∨
      (Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom3739 chi)))))))))) := by
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
                exact fin15Anchored_clause28522 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28523 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28524 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28525 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28526 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28527 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28528 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28529 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28530 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28531 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28532 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28533 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28534 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28535 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28536 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28537 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28538 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28539 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28540 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28541 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28542 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28543 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28544 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28545 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28546 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28547 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28548 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28549 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28550 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28551 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28552 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28553 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28554 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28555 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28556 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28557 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28558 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28559 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28560 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28561 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28562 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28563 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28564 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28565 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28566 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28567 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28568 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28569 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28570 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28571 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28572 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28573 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28574 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28575 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28576 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28577 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28578 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28579 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28580 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28581 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28582 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28583 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28584 chi hnoStrong hbad
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
                exact fin15Anchored_clause28585 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28586 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28587 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28588 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28589 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28590 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28591 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28592 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28593 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28594 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28595 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28596 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28597 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28598 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28599 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28600 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28601 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28602 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28603 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28604 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28605 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28606 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28607 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28608 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28609 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28610 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28611 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28612 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28613 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28614 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28615 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28616 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28617 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28618 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28619 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28620 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28621 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28622 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28623 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28624 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28625 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28626 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28627 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28628 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28629 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28630 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28631 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28632 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28633 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28634 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28635 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28636 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28637 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28638 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28639 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28640 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28641 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28642 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28643 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28644 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28645 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28646 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28647 chi hnoStrong hbad
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
                exact fin15Anchored_clause28648 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28649 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28650 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28651 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28652 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28653 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28654 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28655 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28656 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28657 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28658 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28659 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28660 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28661 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28662 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28663 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28664 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28665 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28666 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28667 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28668 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28669 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28670 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28671 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28672 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28673 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28674 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28675 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28676 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28677 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28678 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28679 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28680 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28681 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28682 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28683 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28684 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28685 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28686 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28687 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28688 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28689 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28690 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28691 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28692 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28693 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28694 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28695 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28696 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28697 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28698 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28699 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28700 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28701 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28702 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28703 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28704 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28705 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28706 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28707 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28708 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28709 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28710 chi hnoStrong hbad
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
                exact fin15Anchored_clause28711 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28712 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28713 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28714 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28715 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28716 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28717 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28718 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28719 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28720 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28721 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28722 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28723 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28724 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28725 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28726 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28727 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28728 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28729 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28730 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28731 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28732 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28733 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28734 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28735 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28736 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28737 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28738 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28739 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28740 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28741 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28742 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28743 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28744 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28745 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28746 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28747 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28748 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28749 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28750 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28751 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28752 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28753 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28754 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28755 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28756 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28757 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28758 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28759 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28760 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28761 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28762 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28763 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28764 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28765 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28766 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28767 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28768 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28769 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28770 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28771 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28772 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28773 chi hnoStrong hbad

end ErdosSzekeres

end
