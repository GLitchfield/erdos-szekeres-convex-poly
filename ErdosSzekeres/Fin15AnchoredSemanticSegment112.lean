module

public import ErdosSzekeres.Fin15AnchoredClauseChunk220
public import ErdosSzekeres.Fin15AnchoredClauseChunk221
public import ErdosSzekeres.Fin15AnchoredClauseChunk222

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 112. -/

theorem fin15Anchored_rejectSemanticSegment112
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom1832 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2885 chi) ∨
      ((Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2886 chi) ∨
      (Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2888 chi))) ∨
      (((Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2889 chi) ∨
      (Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2891 chi)) ∨
      ((Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2892 chi) ∨
      (Fin15AnchoredAtom1833 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2893 chi)))) ∨
      ((((Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2895 chi) ∨
      (Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2896 chi)) ∨
      ((Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2898 chi) ∨
      (Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2899 chi))) ∨
      (((Fin15AnchoredAtom1834 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2900 chi) ∨
      (Fin15AnchoredAtom1835 chi ∧
      Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1866 chi ∧
      Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom2186 chi ∧
      Fin15AnchoredAtom2901 chi)) ∨
      ((Fin15AnchoredAtom1835 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1871 chi ∧
      Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom2191 chi ∧
      Fin15AnchoredAtom2906 chi) ∨
      (Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2907 chi))))) ∨
      (((((Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2909 chi) ∨
      (Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2910 chi)) ∨
      ((Fin15AnchoredAtom1836 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2911 chi) ∨
      (Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2913 chi))) ∨
      (((Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2914 chi) ∨
      (Fin15AnchoredAtom1837 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2915 chi)) ∨
      ((Fin15AnchoredAtom1838 chi ∧
      Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1881 chi ∧
      Fin15AnchoredAtom1981 chi ∧
      Fin15AnchoredAtom2201 chi ∧
      Fin15AnchoredAtom2916 chi) ∨
      (Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2919 chi)))) ∨
      ((((Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2920 chi) ∨
      (Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2921 chi)) ∨
      ((Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2922 chi) ∨
      (Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1844 chi ∧
      Fin15AnchoredAtom1852 chi ∧
      Fin15AnchoredAtom1988 chi ∧
      Fin15AnchoredAtom2208 chi ∧
      Fin15AnchoredAtom2923 chi))) ∨
      (((Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2924 chi) ∨
      (Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2925 chi)) ∨
      ((Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1847 chi ∧
      Fin15AnchoredAtom1855 chi ∧
      Fin15AnchoredAtom1991 chi ∧
      Fin15AnchoredAtom2211 chi ∧
      Fin15AnchoredAtom2926 chi) ∨
      (Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2927 chi)))))) ∨
      ((((((Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2928 chi) ∨
      (Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2929 chi)) ∨
      ((Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1844 chi ∧
      Fin15AnchoredAtom1859 chi ∧
      Fin15AnchoredAtom1995 chi ∧
      Fin15AnchoredAtom2215 chi ∧
      Fin15AnchoredAtom2930 chi) ∨
      (Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2931 chi))) ∨
      (((Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2932 chi) ∨
      (Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2934 chi)) ∨
      ((Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2935 chi) ∨
      (Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2936 chi)))) ∨
      ((((Fin15AnchoredAtom1844 chi ∧
      Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1866 chi ∧
      Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom2222 chi ∧
      Fin15AnchoredAtom2937 chi) ∨
      (Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2943 chi)) ∨
      ((Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2945 chi) ∨
      (Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2946 chi))) ∨
      (((Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2947 chi) ∨
      (Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2949 chi)) ∨
      ((Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2950 chi) ∨
      (Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2951 chi))))) ∨
      (((((Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2955 chi) ∨
      (Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2956 chi)) ∨
      ((Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2957 chi) ∨
      (Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1852 chi ∧
      Fin15AnchoredAtom1859 chi ∧
      Fin15AnchoredAtom2023 chi ∧
      Fin15AnchoredAtom2243 chi ∧
      Fin15AnchoredAtom2958 chi))) ∨
      (((Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2959 chi) ∨
      (Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2960 chi)) ∨
      ((Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2962 chi) ∨
      (Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2963 chi)))) ∨
      ((((Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2964 chi) ∨
      (Fin15AnchoredAtom1852 chi ∧
      Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1866 chi ∧
      Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2250 chi ∧
      Fin15AnchoredAtom2965 chi)) ∨
      ((Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2971 chi) ∨
      (Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2973 chi))) ∨
      (((Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2974 chi) ∨
      (Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2975 chi)) ∨
      ((Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1855 chi ∧
      Fin15AnchoredAtom1877 chi ∧
      Fin15AnchoredAtom2041 chi ∧
      Fin15AnchoredAtom2261 chi ∧
      Fin15AnchoredAtom2976 chi) ∨
      (Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2977 chi))))))) ∨
      ((((((Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2978 chi) ∨
      ((Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2979 chi) ∨
      (Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2983 chi))) ∨
      (((Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2984 chi) ∨
      (Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2985 chi)) ∨
      ((Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2992 chi) ∨
      (Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2994 chi)))) ∨
      ((((Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2995 chi) ∨
      (Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2996 chi)) ∨
      ((Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2998 chi) ∨
      (Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2999 chi))) ∨
      (((Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom3000 chi) ∨
      (Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom3004 chi)) ∨
      ((Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom3005 chi) ∨
      (Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom3006 chi))))) ∨
      (((((Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom3023 chi) ∨
      (Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom3024 chi)) ∨
      ((Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom3025 chi) ∨
      (Fin15AnchoredAtom1873 chi ∧
      Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1881 chi ∧
      Fin15AnchoredAtom2091 chi ∧
      Fin15AnchoredAtom2311 chi ∧
      Fin15AnchoredAtom3026 chi))) ∨
      (((Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom3029 chi) ∨
      (Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom3030 chi)) ∨
      ((Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom3031 chi) ∨
      (Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom3035 chi)))) ∨
      ((((Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom3036 chi) ∨
      (Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom3037 chi)) ∨
      ((Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom3041 chi) ∨
      (Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom3042 chi))) ∨
      (((Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom3043 chi) ∨
      (Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1944 chi ∧
      Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom3044 chi)) ∨
      ((Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom3045 chi) ∨
      (Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom3046 chi)))))) ∨
      ((((((Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom3048 chi) ∨
      (Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom3049 chi)) ∨
      ((Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom3050 chi) ∨
      (Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom3051 chi))) ∨
      (((Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1952 chi ∧
      Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom3052 chi) ∨
      (Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom3053 chi)) ∨
      ((Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom3054 chi) ∨
      (Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom3056 chi)))) ∨
      ((((Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom3057 chi) ∨
      (Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom3058 chi)) ∨
      ((Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom1959 chi ∧
      Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom3059 chi) ∨
      (Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom3060 chi))) ∨
      (((Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom3061 chi) ∨
      (Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom3063 chi)) ∨
      ((Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom3064 chi) ∨
      (Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom3065 chi))))) ∨
      (((((Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom3066 chi) ∨
      (Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom3067 chi)) ∨
      ((Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom1969 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom3069 chi) ∨
      (Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom1970 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom3070 chi))) ∨
      (((Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom3071 chi) ∨
      (Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom3072 chi)) ∨
      ((Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom3074 chi) ∨
      (Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom3075 chi)))) ∨
      ((((Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom3076 chi) ∨
      (Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom3078 chi)) ∨
      ((Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom3079 chi) ∨
      (Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom3080 chi))) ∨
      (((Fin15AnchoredAtom1893 chi ∧
      Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1936 chi ∧
      Fin15AnchoredAtom1981 chi ∧
      Fin15AnchoredAtom2366 chi ∧
      Fin15AnchoredAtom3081 chi) ∨
      (Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom3084 chi)) ∨
      ((Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom3085 chi) ∨
      (Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom3086 chi)))))))) ∨
      (((((((Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom3087 chi) ∨
      ((Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1988 chi ∧
      Fin15AnchoredAtom2373 chi ∧
      Fin15AnchoredAtom3088 chi) ∨
      (Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom3089 chi))) ∨
      (((Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom3090 chi) ∨
      (Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom3092 chi)) ∨
      ((Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom3093 chi) ∨
      (Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom3094 chi)))) ∨
      ((((Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom1995 chi ∧
      Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom3095 chi) ∨
      (Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom3096 chi)) ∨
      ((Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom3097 chi) ∨
      (Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom3099 chi))) ∨
      (((Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom3100 chi) ∨
      (Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom3101 chi)) ∨
      ((Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom3102 chi) ∨
      (Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom2003 chi ∧
      Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom3103 chi))))) ∨
      (((((Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom2005 chi ∧
      Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom3105 chi) ∨
      (Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom2007 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom3107 chi)) ∨
      ((Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom3108 chi) ∨
      (Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom3110 chi))) ∨
      (((Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom3111 chi) ∨
      (Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom3112 chi)) ∨
      ((Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom3114 chi) ∨
      (Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom3115 chi)))) ∨
      ((((Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom3116 chi) ∨
      (Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom3120 chi)) ∨
      ((Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom3121 chi) ∨
      (Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom3122 chi))) ∨
      (((Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom2023 chi ∧
      Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom3123 chi) ∨
      (Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom3124 chi)) ∨
      ((Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom3125 chi) ∨
      (Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom3127 chi)))))) ∨
      ((((((Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom3128 chi) ∨
      (Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom3129 chi)) ∨
      ((Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom3130 chi) ∨
      (Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom3131 chi))) ∨
      (((Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom2035 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom3135 chi) ∨
      (Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom3136 chi)) ∨
      ((Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom3138 chi) ∨
      (Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom3139 chi)))) ∨
      ((((Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom3140 chi) ∨
      (Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom3142 chi)) ∨
      ((Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom3143 chi) ∨
      (Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom3144 chi))) ∨
      (((Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom3148 chi) ∨
      (Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom3149 chi)) ∨
      ((Fin15AnchoredAtom1912 chi ∧
      Fin15AnchoredAtom1913 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom3150 chi) ∨
      (Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom3151 chi))))) ∨
      (((((Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom2052 chi ∧
      Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom3152 chi) ∨
      (Fin15AnchoredAtom1914 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom2056 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom3156 chi)) ∨
      ((Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom3157 chi) ∨
      (Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom3159 chi))) ∨
      (((Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom3160 chi) ∨
      (Fin15AnchoredAtom1915 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom3161 chi)) ∨
      ((Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom3163 chi) ∨
      (Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom3164 chi)))) ∨
      ((((Fin15AnchoredAtom1916 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom3165 chi) ∨
      (Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom3169 chi)) ∨
      ((Fin15AnchoredAtom1918 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom3170 chi) ∨
      (Fin15AnchoredAtom1919 chi ∧
      Fin15AnchoredAtom1920 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom3171 chi))) ∨
      (((Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom3172 chi) ∨
      (Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom3174 chi)) ∨
      ((Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom3175 chi) ∨
      (Fin15AnchoredAtom1921 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom2076 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom3176 chi))))))) ∨
      ((((((Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom3178 chi) ∨
      ((Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom3179 chi) ∨
      (Fin15AnchoredAtom1922 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2080 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom3180 chi))) ∨
      (((Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom3184 chi) ∨
      (Fin15AnchoredAtom1924 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom3185 chi)) ∨
      ((Fin15AnchoredAtom1925 chi ∧
      Fin15AnchoredAtom1926 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom3186 chi) ∨
      (Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom3188 chi)))) ∨
      ((((Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom3189 chi) ∨
      (Fin15AnchoredAtom1927 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom3190 chi)) ∨
      ((Fin15AnchoredAtom1928 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom1937 chi ∧
      Fin15AnchoredAtom2092 chi ∧
      Fin15AnchoredAtom2477 chi ∧
      Fin15AnchoredAtom3192 chi) ∨
      (Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2094 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom3194 chi))) ∨
      (((Fin15AnchoredAtom1929 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2095 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom3195 chi) ∨
      (Fin15AnchoredAtom1930 chi ∧
      Fin15AnchoredAtom1931 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2096 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom3196 chi)) ∨
      ((Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom2100 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom3200 chi) ∨
      (Fin15AnchoredAtom1933 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom2101 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom3201 chi))))) ∨
      (((((Fin15AnchoredAtom1934 chi ∧
      Fin15AnchoredAtom1935 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2102 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom3202 chi) ∨
      (Fin15AnchoredAtom1939 chi ∧
      Fin15AnchoredAtom1940 chi ∧
      Fin15AnchoredAtom1941 chi ∧
      Fin15AnchoredAtom2106 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom3206 chi)) ∨
      ((Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom3207 chi) ∨
      (Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom3209 chi))) ∨
      (((Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom3210 chi) ∨
      (Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom3212 chi)) ∨
      ((Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom3213 chi) ∨
      (Fin15AnchoredAtom1942 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom3214 chi)))) ∨
      ((((Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom3216 chi) ∨
      (Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom3217 chi)) ∨
      ((Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom3219 chi) ∨
      (Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom3220 chi))) ∨
      (((Fin15AnchoredAtom1943 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom3221 chi) ∨
      (Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom3228 chi)) ∨
      ((Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom2010 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom3230 chi) ∨
      (Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom2011 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom3231 chi)))))) ∨
      ((((((Fin15AnchoredAtom1945 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom2012 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom3232 chi) ∨
      (Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2014 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom3234 chi)) ∨
      ((Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2015 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom3235 chi) ∨
      (Fin15AnchoredAtom1946 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2016 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom3236 chi))) ∨
      (((Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2020 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom3240 chi) ∨
      (Fin15AnchoredAtom1948 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2021 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom3241 chi)) ∨
      ((Fin15AnchoredAtom1949 chi ∧
      Fin15AnchoredAtom1950 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2022 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom3242 chi) ∨
      (Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom2024 chi ∧
      Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom3244 chi)))) ∨
      ((((Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom2025 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom3245 chi) ∨
      (Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom2027 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom3247 chi)) ∨
      ((Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom2028 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom3248 chi) ∨
      (Fin15AnchoredAtom1951 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom2029 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom3249 chi))) ∨
      (((Fin15AnchoredAtom1952 chi ∧
      Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom2030 chi ∧
      Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom3250 chi) ∨
      (Fin15AnchoredAtom1952 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom2031 chi ∧
      Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom3251 chi)) ∨
      ((Fin15AnchoredAtom1952 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1969 chi ∧
      Fin15AnchoredAtom2033 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom3253 chi) ∨
      (Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom3256 chi))))) ∨
      (((((Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom3258 chi) ∨
      (Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom3259 chi)) ∨
      ((Fin15AnchoredAtom1953 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom3260 chi) ∨
      (Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom3262 chi))) ∨
      (((Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom3263 chi) ∨
      (Fin15AnchoredAtom1954 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom3264 chi)) ∨
      ((Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom3268 chi) ∨
      (Fin15AnchoredAtom1956 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom3269 chi)))) ∨
      ((((Fin15AnchoredAtom1957 chi ∧
      Fin15AnchoredAtom1958 chi ∧
      Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom3270 chi) ∨
      (Fin15AnchoredAtom1959 chi ∧
      Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom3271 chi)) ∨
      ((Fin15AnchoredAtom1959 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom1970 chi ∧
      Fin15AnchoredAtom2055 chi ∧
      Fin15AnchoredAtom2560 chi ∧
      Fin15AnchoredAtom3275 chi) ∨
      (Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom3277 chi))) ∨
      (((Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom3279 chi) ∨
      (Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom3280 chi)) ∨
      ((Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom3281 chi) ∨
      (Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom3283 chi)))))))))) := by
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
                exact fin15Anchored_clause28270 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28271 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28272 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28273 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28274 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28275 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28276 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28277 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28278 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28279 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28280 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28281 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28282 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28283 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28284 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28285 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28286 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28287 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28288 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28289 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28290 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28291 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28292 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28293 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28294 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28295 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28296 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28297 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28298 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28299 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28300 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28301 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28302 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28303 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28304 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28305 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28306 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28307 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28308 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28309 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28310 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28311 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28312 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28313 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28314 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28315 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28316 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28317 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28318 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28319 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28320 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28321 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28322 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28323 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28324 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28325 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28326 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28327 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28328 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28329 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28330 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28331 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28332 chi hnoStrong hbad
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
                exact fin15Anchored_clause28333 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28334 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28335 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28336 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28337 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28338 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28339 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28340 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28341 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28342 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28343 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28344 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28345 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28346 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28347 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28348 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28349 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28350 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28351 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28352 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28353 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28354 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28355 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28356 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28357 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28358 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28359 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28360 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28361 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28362 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28363 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28364 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28365 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28366 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28367 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28368 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28369 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28370 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28371 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28372 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28373 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28374 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28375 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28376 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28377 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28378 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28379 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28380 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28381 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28382 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28383 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28384 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28385 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28386 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28387 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28388 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28389 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28390 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28391 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28392 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28393 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28394 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28395 chi hnoStrong hbad
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
                exact fin15Anchored_clause28396 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28397 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28398 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28399 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28400 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28401 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28402 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28403 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28404 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28405 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28406 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28407 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28408 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28409 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28410 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28411 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28412 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28413 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28414 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28415 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28416 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28417 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28418 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28419 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28420 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28421 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28422 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28423 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28424 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28425 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28426 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28427 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28428 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28429 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28430 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28431 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28432 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28433 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28434 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28435 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28436 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28437 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28438 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28439 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28440 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28441 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28442 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28443 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28444 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28445 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28446 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28447 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28448 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28449 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28450 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28451 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28452 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28453 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28454 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28455 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28456 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28457 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28458 chi hnoStrong hbad
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
                exact fin15Anchored_clause28459 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28460 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28461 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28462 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28463 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28464 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28465 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28466 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28467 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28468 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28469 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28470 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28471 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28472 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28473 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28474 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28475 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28476 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28477 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28478 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28479 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28480 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28481 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28482 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28483 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28484 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28485 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28486 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28487 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28488 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28489 chi hnoStrong hbad
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
                  exact fin15Anchored_clause28490 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28491 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28492 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28493 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28494 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28495 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28496 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28497 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28498 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28499 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28500 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28501 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28502 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28503 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28504 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28505 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28506 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28507 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28508 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28509 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28510 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28511 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28512 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28513 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28514 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28515 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28516 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28517 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28518 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28519 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause28520 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause28521 chi hnoStrong hbad

end ErdosSzekeres

end
