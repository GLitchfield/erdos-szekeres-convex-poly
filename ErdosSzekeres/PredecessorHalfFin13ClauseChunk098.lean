module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 098. -/

theorem predecessorHalfFin13_clause28251 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2024
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2095
    PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2102
    PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2112
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2129
    PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2148
    PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2237
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2268 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28252 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom2269 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 7, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3048
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2096
    PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2100 PredecessorHalfFin13Atom2103
    PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2110 PredecessorHalfFin13Atom2113
    PredecessorHalfFin13Atom2119 PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2130
    PredecessorHalfFin13Atom2133 PredecessorHalfFin13Atom2139 PredecessorHalfFin13Atom2149
    PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2235 PredecessorHalfFin13Atom2238
    PredecessorHalfFin13Atom2244 PredecessorHalfFin13Atom2254 PredecessorHalfFin13Atom2269 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28253 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5096
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2097
    PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2101 PredecessorHalfFin13Atom2104
    PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2111 PredecessorHalfFin13Atom2114
    PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2131
    PredecessorHalfFin13Atom2134 PredecessorHalfFin13Atom2140 PredecessorHalfFin13Atom2150
    PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2236 PredecessorHalfFin13Atom2239
    PredecessorHalfFin13Atom2245 PredecessorHalfFin13Atom2255 PredecessorHalfFin13Atom2270 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28254 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom2271 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 7, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3560
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2096
    PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2100 PredecessorHalfFin13Atom2105
    PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2110 PredecessorHalfFin13Atom2115
    PredecessorHalfFin13Atom2121 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2130
    PredecessorHalfFin13Atom2135 PredecessorHalfFin13Atom2141 PredecessorHalfFin13Atom2151
    PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2235 PredecessorHalfFin13Atom2240
    PredecessorHalfFin13Atom2246 PredecessorHalfFin13Atom2256 PredecessorHalfFin13Atom2271 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28255 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5608
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2097
    PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2101 PredecessorHalfFin13Atom2106
    PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2111 PredecessorHalfFin13Atom2116
    PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2131
    PredecessorHalfFin13Atom2136 PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2152
    PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2236 PredecessorHalfFin13Atom2241
    PredecessorHalfFin13Atom2247 PredecessorHalfFin13Atom2257 PredecessorHalfFin13Atom2272 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28257 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom2274 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3816
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2096
    PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2103 PredecessorHalfFin13Atom2105
    PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2113 PredecessorHalfFin13Atom2115
    PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2133
    PredecessorHalfFin13Atom2135 PredecessorHalfFin13Atom2144 PredecessorHalfFin13Atom2154
    PredecessorHalfFin13Atom2237 PredecessorHalfFin13Atom2238 PredecessorHalfFin13Atom2240
    PredecessorHalfFin13Atom2249 PredecessorHalfFin13Atom2259 PredecessorHalfFin13Atom2274 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28258 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5864
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2097
    PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2104 PredecessorHalfFin13Atom2106
    PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2116
    PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2134
    PredecessorHalfFin13Atom2136 PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2155
    PredecessorHalfFin13Atom2237 PredecessorHalfFin13Atom2239 PredecessorHalfFin13Atom2241
    PredecessorHalfFin13Atom2250 PredecessorHalfFin13Atom2260 PredecessorHalfFin13Atom2275 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28259 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom2261 chi ∧
      ¬PredecessorHalfFin13Atom2276 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 7, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6888
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2096 PredecessorHalfFin13Atom2097
    PredecessorHalfFin13Atom2103 PredecessorHalfFin13Atom2104 PredecessorHalfFin13Atom2107
    PredecessorHalfFin13Atom2113 PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2117
    PredecessorHalfFin13Atom2126 PredecessorHalfFin13Atom2133 PredecessorHalfFin13Atom2134
    PredecessorHalfFin13Atom2137 PredecessorHalfFin13Atom2146 PredecessorHalfFin13Atom2156
    PredecessorHalfFin13Atom2238 PredecessorHalfFin13Atom2239 PredecessorHalfFin13Atom2242
    PredecessorHalfFin13Atom2251 PredecessorHalfFin13Atom2261 PredecessorHalfFin13Atom2276 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28260 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom2262 chi ∧
      ¬PredecessorHalfFin13Atom2277 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 7, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7400
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2096 PredecessorHalfFin13Atom2097
    PredecessorHalfFin13Atom2105 PredecessorHalfFin13Atom2106 PredecessorHalfFin13Atom2107
    PredecessorHalfFin13Atom2115 PredecessorHalfFin13Atom2116 PredecessorHalfFin13Atom2117
    PredecessorHalfFin13Atom2127 PredecessorHalfFin13Atom2135 PredecessorHalfFin13Atom2136
    PredecessorHalfFin13Atom2137 PredecessorHalfFin13Atom2147 PredecessorHalfFin13Atom2157
    PredecessorHalfFin13Atom2240 PredecessorHalfFin13Atom2241 PredecessorHalfFin13Atom2242
    PredecessorHalfFin13Atom2252 PredecessorHalfFin13Atom2262 PredecessorHalfFin13Atom2277 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28261 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom2278 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3944
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2100
    PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2103 PredecessorHalfFin13Atom2105
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2119 PredecessorHalfFin13Atom2121
    PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2139
    PredecessorHalfFin13Atom2141 PredecessorHalfFin13Atom2144 PredecessorHalfFin13Atom2158
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2244 PredecessorHalfFin13Atom2246
    PredecessorHalfFin13Atom2249 PredecessorHalfFin13Atom2263 PredecessorHalfFin13Atom2278 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28262 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5992
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2101
    PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2104 PredecessorHalfFin13Atom2106
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2122
    PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2140
    PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2159
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2245 PredecessorHalfFin13Atom2247
    PredecessorHalfFin13Atom2250 PredecessorHalfFin13Atom2264 PredecessorHalfFin13Atom2279 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28263 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom2265 chi ∧
      ¬PredecessorHalfFin13Atom2280 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 8, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7016
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2100 PredecessorHalfFin13Atom2101
    PredecessorHalfFin13Atom2103 PredecessorHalfFin13Atom2104 PredecessorHalfFin13Atom2107
    PredecessorHalfFin13Atom2119 PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2123
    PredecessorHalfFin13Atom2126 PredecessorHalfFin13Atom2139 PredecessorHalfFin13Atom2140
    PredecessorHalfFin13Atom2143 PredecessorHalfFin13Atom2146 PredecessorHalfFin13Atom2160
    PredecessorHalfFin13Atom2244 PredecessorHalfFin13Atom2245 PredecessorHalfFin13Atom2248
    PredecessorHalfFin13Atom2251 PredecessorHalfFin13Atom2265 PredecessorHalfFin13Atom2280 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28264 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom2281 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 6, 8, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7528
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2100 PredecessorHalfFin13Atom2101
    PredecessorHalfFin13Atom2105 PredecessorHalfFin13Atom2106 PredecessorHalfFin13Atom2107
    PredecessorHalfFin13Atom2121 PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2123
    PredecessorHalfFin13Atom2127 PredecessorHalfFin13Atom2141 PredecessorHalfFin13Atom2142
    PredecessorHalfFin13Atom2143 PredecessorHalfFin13Atom2147 PredecessorHalfFin13Atom2161
    PredecessorHalfFin13Atom2246 PredecessorHalfFin13Atom2247 PredecessorHalfFin13Atom2248
    PredecessorHalfFin13Atom2252 PredecessorHalfFin13Atom2266 PredecessorHalfFin13Atom2281 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28266 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 7, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4008
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2110
    PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2113 PredecessorHalfFin13Atom2115
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2119 PredecessorHalfFin13Atom2121
    PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2149
    PredecessorHalfFin13Atom2151 PredecessorHalfFin13Atom2154 PredecessorHalfFin13Atom2158
    PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2254 PredecessorHalfFin13Atom2256
    PredecessorHalfFin13Atom2259 PredecessorHalfFin13Atom2263 PredecessorHalfFin13Atom2283 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28267 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6056
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2111
    PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2116
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2122
    PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2150
    PredecessorHalfFin13Atom2152 PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2159
    PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2255 PredecessorHalfFin13Atom2257
    PredecessorHalfFin13Atom2260 PredecessorHalfFin13Atom2264 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28269 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2258 chi ∧
      ¬PredecessorHalfFin13Atom2262 chi ∧
      ¬PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom2286 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 7, 8, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7592
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2110 PredecessorHalfFin13Atom2111
    PredecessorHalfFin13Atom2115 PredecessorHalfFin13Atom2116 PredecessorHalfFin13Atom2117
    PredecessorHalfFin13Atom2121 PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2123
    PredecessorHalfFin13Atom2127 PredecessorHalfFin13Atom2151 PredecessorHalfFin13Atom2152
    PredecessorHalfFin13Atom2153 PredecessorHalfFin13Atom2157 PredecessorHalfFin13Atom2161
    PredecessorHalfFin13Atom2256 PredecessorHalfFin13Atom2257 PredecessorHalfFin13Atom2258
    PredecessorHalfFin13Atom2262 PredecessorHalfFin13Atom2266 PredecessorHalfFin13Atom2286 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28270 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2261 chi ∧
      ¬PredecessorHalfFin13Atom2262 chi ∧
      ¬PredecessorHalfFin13Atom2267 chi ∧
      ¬PredecessorHalfFin13Atom2287 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 7, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7848
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2113 PredecessorHalfFin13Atom2114
    PredecessorHalfFin13Atom2115 PredecessorHalfFin13Atom2116 PredecessorHalfFin13Atom2117
    PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2126
    PredecessorHalfFin13Atom2127 PredecessorHalfFin13Atom2154 PredecessorHalfFin13Atom2155
    PredecessorHalfFin13Atom2156 PredecessorHalfFin13Atom2157 PredecessorHalfFin13Atom2162
    PredecessorHalfFin13Atom2259 PredecessorHalfFin13Atom2260 PredecessorHalfFin13Atom2261
    PredecessorHalfFin13Atom2262 PredecessorHalfFin13Atom2267 PredecessorHalfFin13Atom2287 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28271 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2265 chi ∧
      ¬PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom2267 chi ∧
      ¬PredecessorHalfFin13Atom2288 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 5, 8, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7976
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2119 PredecessorHalfFin13Atom2120
    PredecessorHalfFin13Atom2121 PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2123
    PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2126
    PredecessorHalfFin13Atom2127 PredecessorHalfFin13Atom2158 PredecessorHalfFin13Atom2159
    PredecessorHalfFin13Atom2160 PredecessorHalfFin13Atom2161 PredecessorHalfFin13Atom2162
    PredecessorHalfFin13Atom2263 PredecessorHalfFin13Atom2264 PredecessorHalfFin13Atom2265
    PredecessorHalfFin13Atom2266 PredecessorHalfFin13Atom2267 PredecessorHalfFin13Atom2288 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28272 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 6, 7, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4040
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2130
    PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2133 PredecessorHalfFin13Atom2135
    PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2139 PredecessorHalfFin13Atom2141
    PredecessorHalfFin13Atom2144 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2149
    PredecessorHalfFin13Atom2151 PredecessorHalfFin13Atom2154 PredecessorHalfFin13Atom2158
    PredecessorHalfFin13Atom2268 PredecessorHalfFin13Atom2269 PredecessorHalfFin13Atom2271
    PredecessorHalfFin13Atom2274 PredecessorHalfFin13Atom2278 PredecessorHalfFin13Atom2283 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28273 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 6, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6088
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2131
    PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2134 PredecessorHalfFin13Atom2136
    PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2140 PredecessorHalfFin13Atom2142
    PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2150
    PredecessorHalfFin13Atom2152 PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2159
    PredecessorHalfFin13Atom2268 PredecessorHalfFin13Atom2270 PredecessorHalfFin13Atom2272
    PredecessorHalfFin13Atom2275 PredecessorHalfFin13Atom2279 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28275 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom2273 chi ∧
      ¬PredecessorHalfFin13Atom2277 chi ∧
      ¬PredecessorHalfFin13Atom2281 chi ∧
      ¬PredecessorHalfFin13Atom2286 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 6, 7, 8, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7624
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2130 PredecessorHalfFin13Atom2131
    PredecessorHalfFin13Atom2135 PredecessorHalfFin13Atom2136 PredecessorHalfFin13Atom2137
    PredecessorHalfFin13Atom2141 PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2143
    PredecessorHalfFin13Atom2147 PredecessorHalfFin13Atom2151 PredecessorHalfFin13Atom2152
    PredecessorHalfFin13Atom2153 PredecessorHalfFin13Atom2157 PredecessorHalfFin13Atom2161
    PredecessorHalfFin13Atom2271 PredecessorHalfFin13Atom2272 PredecessorHalfFin13Atom2273
    PredecessorHalfFin13Atom2277 PredecessorHalfFin13Atom2281 PredecessorHalfFin13Atom2286 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28277 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom2280 chi ∧
      ¬PredecessorHalfFin13Atom2281 chi ∧
      ¬PredecessorHalfFin13Atom2282 chi ∧
      ¬PredecessorHalfFin13Atom2288 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 6, 8, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask8008
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2139 PredecessorHalfFin13Atom2140
    PredecessorHalfFin13Atom2141 PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2143
    PredecessorHalfFin13Atom2144 PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2146
    PredecessorHalfFin13Atom2147 PredecessorHalfFin13Atom2158 PredecessorHalfFin13Atom2159
    PredecessorHalfFin13Atom2160 PredecessorHalfFin13Atom2161 PredecessorHalfFin13Atom2162
    PredecessorHalfFin13Atom2278 PredecessorHalfFin13Atom2279 PredecessorHalfFin13Atom2280
    PredecessorHalfFin13Atom2281 PredecessorHalfFin13Atom2282 PredecessorHalfFin13Atom2288 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28279 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2032
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2165
    PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2172
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2182
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2199
    PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2218
    PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2237
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2268 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28280 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom2269 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 6, 7, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3056
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2166
    PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2170 PredecessorHalfFin13Atom2173
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2180 PredecessorHalfFin13Atom2183
    PredecessorHalfFin13Atom2189 PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2200
    PredecessorHalfFin13Atom2203 PredecessorHalfFin13Atom2209 PredecessorHalfFin13Atom2219
    PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2235 PredecessorHalfFin13Atom2238
    PredecessorHalfFin13Atom2244 PredecessorHalfFin13Atom2254 PredecessorHalfFin13Atom2269 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28281 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5104
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2167
    PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2171 PredecessorHalfFin13Atom2174
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2184
    PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2201
    PredecessorHalfFin13Atom2204 PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2220
    PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2236 PredecessorHalfFin13Atom2239
    PredecessorHalfFin13Atom2245 PredecessorHalfFin13Atom2255 PredecessorHalfFin13Atom2270 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28282 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom2271 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 6, 7, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3568
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2166
    PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2170 PredecessorHalfFin13Atom2175
    PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2180 PredecessorHalfFin13Atom2185
    PredecessorHalfFin13Atom2191 PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2200
    PredecessorHalfFin13Atom2205 PredecessorHalfFin13Atom2211 PredecessorHalfFin13Atom2221
    PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2235 PredecessorHalfFin13Atom2240
    PredecessorHalfFin13Atom2246 PredecessorHalfFin13Atom2256 PredecessorHalfFin13Atom2271 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28283 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5616
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2167
    PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2171 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2186
    PredecessorHalfFin13Atom2192 PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2201
    PredecessorHalfFin13Atom2206 PredecessorHalfFin13Atom2212 PredecessorHalfFin13Atom2222
    PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2236 PredecessorHalfFin13Atom2241
    PredecessorHalfFin13Atom2247 PredecessorHalfFin13Atom2257 PredecessorHalfFin13Atom2272 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28284 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2187 chi ∧
      ¬PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom2258 chi ∧
      ¬PredecessorHalfFin13Atom2273 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 6, 7, 8, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6640
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2166 PredecessorHalfFin13Atom2167
    PredecessorHalfFin13Atom2170 PredecessorHalfFin13Atom2171 PredecessorHalfFin13Atom2177
    PredecessorHalfFin13Atom2180 PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2187
    PredecessorHalfFin13Atom2193 PredecessorHalfFin13Atom2200 PredecessorHalfFin13Atom2201
    PredecessorHalfFin13Atom2207 PredecessorHalfFin13Atom2213 PredecessorHalfFin13Atom2223
    PredecessorHalfFin13Atom2235 PredecessorHalfFin13Atom2236 PredecessorHalfFin13Atom2242
    PredecessorHalfFin13Atom2248 PredecessorHalfFin13Atom2258 PredecessorHalfFin13Atom2273 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28285 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom2274 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 6, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3824
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2166
    PredecessorHalfFin13Atom2172 PredecessorHalfFin13Atom2173 PredecessorHalfFin13Atom2175
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2183 PredecessorHalfFin13Atom2185
    PredecessorHalfFin13Atom2194 PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2203
    PredecessorHalfFin13Atom2205 PredecessorHalfFin13Atom2214 PredecessorHalfFin13Atom2224
    PredecessorHalfFin13Atom2237 PredecessorHalfFin13Atom2238 PredecessorHalfFin13Atom2240
    PredecessorHalfFin13Atom2249 PredecessorHalfFin13Atom2259 PredecessorHalfFin13Atom2274 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28286 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5872
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2167
    PredecessorHalfFin13Atom2172 PredecessorHalfFin13Atom2174 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2184 PredecessorHalfFin13Atom2186
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2204
    PredecessorHalfFin13Atom2206 PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2225
    PredecessorHalfFin13Atom2237 PredecessorHalfFin13Atom2239 PredecessorHalfFin13Atom2241
    PredecessorHalfFin13Atom2250 PredecessorHalfFin13Atom2260 PredecessorHalfFin13Atom2275 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28290 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6000
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2171
    PredecessorHalfFin13Atom2172 PredecessorHalfFin13Atom2174 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2192
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2210
    PredecessorHalfFin13Atom2212 PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2229
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2245 PredecessorHalfFin13Atom2247
    PredecessorHalfFin13Atom2250 PredecessorHalfFin13Atom2264 PredecessorHalfFin13Atom2279 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28292 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom2281 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 6, 8, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7536
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2170 PredecessorHalfFin13Atom2171
    PredecessorHalfFin13Atom2175 PredecessorHalfFin13Atom2176 PredecessorHalfFin13Atom2177
    PredecessorHalfFin13Atom2191 PredecessorHalfFin13Atom2192 PredecessorHalfFin13Atom2193
    PredecessorHalfFin13Atom2197 PredecessorHalfFin13Atom2211 PredecessorHalfFin13Atom2212
    PredecessorHalfFin13Atom2213 PredecessorHalfFin13Atom2217 PredecessorHalfFin13Atom2231
    PredecessorHalfFin13Atom2246 PredecessorHalfFin13Atom2247 PredecessorHalfFin13Atom2248
    PredecessorHalfFin13Atom2252 PredecessorHalfFin13Atom2266 PredecessorHalfFin13Atom2281 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28294 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 7, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4016
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2180
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2183 PredecessorHalfFin13Atom2185
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2189 PredecessorHalfFin13Atom2191
    PredecessorHalfFin13Atom2194 PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2219
    PredecessorHalfFin13Atom2221 PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2228
    PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2254 PredecessorHalfFin13Atom2256
    PredecessorHalfFin13Atom2259 PredecessorHalfFin13Atom2263 PredecessorHalfFin13Atom2283 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28295 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 5, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6064
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2181
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2184 PredecessorHalfFin13Atom2186
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2192
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2220
    PredecessorHalfFin13Atom2222 PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2229
    PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2255 PredecessorHalfFin13Atom2257
    PredecessorHalfFin13Atom2260 PredecessorHalfFin13Atom2264 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28300 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 6, 7, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4048
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2200
    PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2203 PredecessorHalfFin13Atom2205
    PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2209 PredecessorHalfFin13Atom2211
    PredecessorHalfFin13Atom2214 PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2219
    PredecessorHalfFin13Atom2221 PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2228
    PredecessorHalfFin13Atom2268 PredecessorHalfFin13Atom2269 PredecessorHalfFin13Atom2271
    PredecessorHalfFin13Atom2274 PredecessorHalfFin13Atom2278 PredecessorHalfFin13Atom2283 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28301 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 6, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6096
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2201
    PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2204 PredecessorHalfFin13Atom2206
    PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2212
    PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2220
    PredecessorHalfFin13Atom2222 PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2229
    PredecessorHalfFin13Atom2268 PredecessorHalfFin13Atom2270 PredecessorHalfFin13Atom2272
    PredecessorHalfFin13Atom2275 PredecessorHalfFin13Atom2279 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28304 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom2276 chi ∧
      ¬PredecessorHalfFin13Atom2277 chi ∧
      ¬PredecessorHalfFin13Atom2282 chi ∧
      ¬PredecessorHalfFin13Atom2287 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 6, 7, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7888
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2203 PredecessorHalfFin13Atom2204
    PredecessorHalfFin13Atom2205 PredecessorHalfFin13Atom2206 PredecessorHalfFin13Atom2207
    PredecessorHalfFin13Atom2214 PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2216
    PredecessorHalfFin13Atom2217 PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2225
    PredecessorHalfFin13Atom2226 PredecessorHalfFin13Atom2227 PredecessorHalfFin13Atom2232
    PredecessorHalfFin13Atom2274 PredecessorHalfFin13Atom2275 PredecessorHalfFin13Atom2276
    PredecessorHalfFin13Atom2277 PredecessorHalfFin13Atom2282 PredecessorHalfFin13Atom2287 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28306 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi ∧
      ¬PredecessorHalfFin13Atom2285 chi ∧
      ¬PredecessorHalfFin13Atom2286 chi ∧
      ¬PredecessorHalfFin13Atom2287 chi ∧
      ¬PredecessorHalfFin13Atom2288 chi) := by
  intro hbad
  apply hno
  refine ⟨{4, 7, 8, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask8080
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2219 PredecessorHalfFin13Atom2220
    PredecessorHalfFin13Atom2221 PredecessorHalfFin13Atom2222 PredecessorHalfFin13Atom2223
    PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2226
    PredecessorHalfFin13Atom2227 PredecessorHalfFin13Atom2228 PredecessorHalfFin13Atom2229
    PredecessorHalfFin13Atom2230 PredecessorHalfFin13Atom2231 PredecessorHalfFin13Atom2232
    PredecessorHalfFin13Atom2283 PredecessorHalfFin13Atom2284 PredecessorHalfFin13Atom2285
    PredecessorHalfFin13Atom2286 PredecessorHalfFin13Atom2287 PredecessorHalfFin13Atom2288 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28307 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi) := by
  intro hbad
  apply hno
  refine ⟨{5, 6, 7, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4064
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2235
    PredecessorHalfFin13Atom2237 PredecessorHalfFin13Atom2238 PredecessorHalfFin13Atom2240
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2244 PredecessorHalfFin13Atom2246
    PredecessorHalfFin13Atom2249 PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2254
    PredecessorHalfFin13Atom2256 PredecessorHalfFin13Atom2259 PredecessorHalfFin13Atom2263
    PredecessorHalfFin13Atom2268 PredecessorHalfFin13Atom2269 PredecessorHalfFin13Atom2271
    PredecessorHalfFin13Atom2274 PredecessorHalfFin13Atom2278 PredecessorHalfFin13Atom2283 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28308 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{5, 6, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6112
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2236
    PredecessorHalfFin13Atom2237 PredecessorHalfFin13Atom2239 PredecessorHalfFin13Atom2241
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2245 PredecessorHalfFin13Atom2247
    PredecessorHalfFin13Atom2250 PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2255
    PredecessorHalfFin13Atom2257 PredecessorHalfFin13Atom2260 PredecessorHalfFin13Atom2264
    PredecessorHalfFin13Atom2268 PredecessorHalfFin13Atom2270 PredecessorHalfFin13Atom2272
    PredecessorHalfFin13Atom2275 PredecessorHalfFin13Atom2279 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28312 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2265 chi ∧
      ¬PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom2267 chi ∧
      ¬PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom2280 chi ∧
      ¬PredecessorHalfFin13Atom2281 chi ∧
      ¬PredecessorHalfFin13Atom2282 chi ∧
      ¬PredecessorHalfFin13Atom2288 chi) := by
  intro hbad
  apply hno
  refine ⟨{5, 6, 8, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask8032
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2244 PredecessorHalfFin13Atom2245
    PredecessorHalfFin13Atom2246 PredecessorHalfFin13Atom2247 PredecessorHalfFin13Atom2248
    PredecessorHalfFin13Atom2249 PredecessorHalfFin13Atom2250 PredecessorHalfFin13Atom2251
    PredecessorHalfFin13Atom2252 PredecessorHalfFin13Atom2263 PredecessorHalfFin13Atom2264
    PredecessorHalfFin13Atom2265 PredecessorHalfFin13Atom2266 PredecessorHalfFin13Atom2267
    PredecessorHalfFin13Atom2278 PredecessorHalfFin13Atom2279 PredecessorHalfFin13Atom2280
    PredecessorHalfFin13Atom2281 PredecessorHalfFin13Atom2282 PredecessorHalfFin13Atom2288 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

end ErdosSzekeres

end
