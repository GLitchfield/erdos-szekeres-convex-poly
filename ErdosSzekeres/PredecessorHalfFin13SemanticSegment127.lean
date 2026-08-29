module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk097
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk098

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 127. -/

theorem predecessorHalfFin13_rejectSemanticSegment127
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom2266 chi ∧
      ¬PredecessorHalfFin13Atom2281 chi) ∨
      ((¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi) ∨
      (¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi))) ∨
      ((¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2261 chi ∧
      ¬PredecessorHalfFin13Atom2262 chi ∧
      ¬PredecessorHalfFin13Atom2267 chi ∧
      ¬PredecessorHalfFin13Atom2287 chi) ∨
      ((¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom2269 chi ∧
      ¬PredecessorHalfFin13Atom2271 chi ∧
      ¬PredecessorHalfFin13Atom2274 chi ∧
      ¬PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi) ∨
      (¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2034 chi ∧
      ¬PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom2278 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom2280 chi ∧
      ¬PredecessorHalfFin13Atom2281 chi ∧
      ¬PredecessorHalfFin13Atom2282 chi ∧
      ¬PredecessorHalfFin13Atom2288 chi) ∨
      ((¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2034 chi ∧
      ¬PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi ∧
      ¬PredecessorHalfFin13Atom2285 chi ∧
      ¬PredecessorHalfFin13Atom2286 chi ∧
      ¬PredecessorHalfFin13Atom2287 chi ∧
      ¬PredecessorHalfFin13Atom2288 chi) ∨
      (¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi))) ∨
      ((¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi) ∨
      ((¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi) ∨
      (¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi) ∨
      ((¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi) ∨
      (¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi))) ∨
      ((¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi) ∨
      ((¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi) ∨
      (¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom2244 chi) ∨
      ((¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi) ∨
      (¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi))) ∨
      ((¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi) ∨
      ((¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom2249 chi) ∨
      (¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom2251 chi) ∨
      ((¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom2252 chi) ∨
      (¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi))) ∨
      ((¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom2254 chi) ∨
      ((¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi) ∨
      (¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom2256 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi) ∨
      ((¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi) ∨
      (¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi))) ∨
      ((¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2187 chi ∧
      ¬PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom2261 chi) ∨
      ((¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom2263 chi) ∨
      (¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom2265 chi) ∨
      ((¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom2267 chi) ∨
      (¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi))) ∨
      ((¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom2269 chi) ∨
      ((¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi) ∨
      (¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom2271 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) ∨
      ((¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom2273 chi) ∨
      (¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2274 chi))) ∨
      (((¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) ∨
      (¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom2276 chi)) ∨
      ((¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom2277 chi) ∨
      (¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom2278 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi) ∨
      ((¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom2280 chi) ∨
      (¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom2281 chi))) ∨
      ((¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom2282 chi) ∨
      ((¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi) ∨
      (¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom2285 chi) ∨
      ((¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom2287 chi) ∨
      (¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom2288 chi))) ∨
      ((¬PredecessorHalfFin13Atom2093 chi ∧
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
      ¬PredecessorHalfFin13Atom2268 chi) ∨
      ((¬PredecessorHalfFin13Atom2093 chi ∧
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
      ¬PredecessorHalfFin13Atom2269 chi) ∨
      (¬PredecessorHalfFin13Atom2093 chi ∧
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
      ¬PredecessorHalfFin13Atom2270 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom2093 chi ∧
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
      ¬PredecessorHalfFin13Atom2271 chi) ∨
      ((¬PredecessorHalfFin13Atom2093 chi ∧
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
      ¬PredecessorHalfFin13Atom2272 chi) ∨
      (¬PredecessorHalfFin13Atom2094 chi ∧
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
      ¬PredecessorHalfFin13Atom2274 chi))) ∨
      ((¬PredecessorHalfFin13Atom2094 chi ∧
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
      ¬PredecessorHalfFin13Atom2275 chi) ∨
      ((¬PredecessorHalfFin13Atom2094 chi ∧
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
      ¬PredecessorHalfFin13Atom2276 chi) ∨
      (¬PredecessorHalfFin13Atom2095 chi ∧
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
      ¬PredecessorHalfFin13Atom2277 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2098 chi ∧
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
      ¬PredecessorHalfFin13Atom2278 chi) ∨
      ((¬PredecessorHalfFin13Atom2098 chi ∧
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
      ¬PredecessorHalfFin13Atom2279 chi) ∨
      (¬PredecessorHalfFin13Atom2098 chi ∧
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
      ¬PredecessorHalfFin13Atom2280 chi))) ∨
      (((¬PredecessorHalfFin13Atom2099 chi ∧
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
      ¬PredecessorHalfFin13Atom2281 chi) ∨
      (¬PredecessorHalfFin13Atom2108 chi ∧
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
      ¬PredecessorHalfFin13Atom2283 chi)) ∨
      ((¬PredecessorHalfFin13Atom2108 chi ∧
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
      ¬PredecessorHalfFin13Atom2284 chi) ∨
      (¬PredecessorHalfFin13Atom2109 chi ∧
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
      ¬PredecessorHalfFin13Atom2286 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom2112 chi ∧
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
      ¬PredecessorHalfFin13Atom2287 chi) ∨
      ((¬PredecessorHalfFin13Atom2118 chi ∧
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
      ¬PredecessorHalfFin13Atom2288 chi) ∨
      (¬PredecessorHalfFin13Atom2128 chi ∧
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
      ¬PredecessorHalfFin13Atom2283 chi))) ∨
      ((¬PredecessorHalfFin13Atom2128 chi ∧
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
      ¬PredecessorHalfFin13Atom2284 chi) ∨
      ((¬PredecessorHalfFin13Atom2129 chi ∧
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
      ¬PredecessorHalfFin13Atom2286 chi) ∨
      (¬PredecessorHalfFin13Atom2138 chi ∧
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
      ¬PredecessorHalfFin13Atom2288 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2163 chi ∧
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
      ¬PredecessorHalfFin13Atom2268 chi) ∨
      ((¬PredecessorHalfFin13Atom2163 chi ∧
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
      ¬PredecessorHalfFin13Atom2269 chi) ∨
      (¬PredecessorHalfFin13Atom2163 chi ∧
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
      ¬PredecessorHalfFin13Atom2270 chi))) ∨
      ((¬PredecessorHalfFin13Atom2163 chi ∧
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
      ¬PredecessorHalfFin13Atom2271 chi) ∨
      ((¬PredecessorHalfFin13Atom2163 chi ∧
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
      ¬PredecessorHalfFin13Atom2272 chi) ∨
      (¬PredecessorHalfFin13Atom2163 chi ∧
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
      ¬PredecessorHalfFin13Atom2273 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom2164 chi ∧
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
      ¬PredecessorHalfFin13Atom2274 chi) ∨
      ((¬PredecessorHalfFin13Atom2164 chi ∧
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
      ¬PredecessorHalfFin13Atom2275 chi) ∨
      (¬PredecessorHalfFin13Atom2168 chi ∧
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
      ¬PredecessorHalfFin13Atom2279 chi))) ∨
      ((¬PredecessorHalfFin13Atom2169 chi ∧
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
      ¬PredecessorHalfFin13Atom2281 chi) ∨
      ((¬PredecessorHalfFin13Atom2178 chi ∧
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
      ¬PredecessorHalfFin13Atom2283 chi) ∨
      (¬PredecessorHalfFin13Atom2178 chi ∧
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
      ¬PredecessorHalfFin13Atom2284 chi)))) ∨
      (((¬PredecessorHalfFin13Atom2198 chi ∧
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
      ¬PredecessorHalfFin13Atom2283 chi) ∨
      ((¬PredecessorHalfFin13Atom2198 chi ∧
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
      ¬PredecessorHalfFin13Atom2284 chi) ∨
      (¬PredecessorHalfFin13Atom2202 chi ∧
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
      ¬PredecessorHalfFin13Atom2287 chi))) ∨
      (((¬PredecessorHalfFin13Atom2218 chi ∧
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
      ¬PredecessorHalfFin13Atom2288 chi) ∨
      (¬PredecessorHalfFin13Atom2233 chi ∧
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
      ¬PredecessorHalfFin13Atom2283 chi)) ∨
      ((¬PredecessorHalfFin13Atom2233 chi ∧
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
      ¬PredecessorHalfFin13Atom2284 chi) ∨
      (¬PredecessorHalfFin13Atom2243 chi ∧
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
      ¬PredecessorHalfFin13Atom2288 chi))))))))) := by
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
              exact predecessorHalfFin13_clause28180 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28182 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28183 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28186 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28188 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28189 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28193 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28194 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28195 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28196 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28197 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28198 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28199 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28200 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28201 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28202 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28203 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28205 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28206 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28207 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28208 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28209 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28211 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28212 chi hno hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28213 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28214 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28215 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28216 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28217 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28218 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28219 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28221 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28222 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28223 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28225 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28226 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28227 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28229 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28230 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28231 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28232 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28233 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28234 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28235 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28236 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28237 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28238 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28239 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28240 chi hno hbad
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
              exact predecessorHalfFin13_clause28241 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28242 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28243 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28244 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28245 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28246 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28247 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28249 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28250 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28251 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28252 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28253 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28254 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28255 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28257 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28258 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28259 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28260 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28261 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28262 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28263 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28264 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28266 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28267 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28269 chi hno hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28270 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28271 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28272 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28273 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28275 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28277 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28279 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28280 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28281 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28282 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28283 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28284 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28285 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28286 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28290 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28292 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28294 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28295 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28300 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28301 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28304 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28306 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28307 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28308 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28312 chi hno hbad

end ErdosSzekeres

end
