module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk096
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk097

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 126. -/

theorem predecessorHalfFin13_rejectSemanticSegment126
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi) ∨
      ((¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi) ∨
      (¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi))) ∨
      ((¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom2244 chi) ∨
      ((¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi) ∨
      (¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi) ∨
      ((¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom2248 chi) ∨
      (¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2249 chi))) ∨
      ((¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi) ∨
      ((¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom2252 chi) ∨
      (¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi) ∨
      ((¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2256 chi) ∨
      (¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi))) ∨
      ((¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi) ∨
      ((¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi) ∨
      (¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom2261 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom2262 chi) ∨
      ((¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom2263 chi) ∨
      (¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi))) ∨
      ((¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom2267 chi) ∨
      ((¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) ∨
      (¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2269 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi) ∨
      ((¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2271 chi) ∨
      (¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi))) ∨
      ((¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2011 chi ∧
      ¬PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom2273 chi) ∨
      ((¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2274 chi) ∨
      (¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2011 chi ∧
      ¬PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom2276 chi) ∨
      ((¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi) ∨
      (¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi))) ∨
      ((¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) ∨
      ((¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom2034 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom2285 chi) ∨
      (¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom2286 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom2287 chi) ∨
      ((¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi) ∨
      (¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi))) ∨
      ((¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi) ∨
      ((¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi) ∨
      (¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi) ∨
      ((¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi) ∨
      (¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi))) ∨
      (((¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi) ∨
      (¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi)) ∨
      ((¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom2244 chi) ∨
      (¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi))))))) ∨
      ((((((¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi) ∨
      ((¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi) ∨
      (¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom2248 chi))) ∨
      ((¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom2249 chi) ∨
      ((¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi) ∨
      (¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom2251 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi) ∨
      ((¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom2254 chi) ∨
      (¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi))) ∨
      ((¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom2256 chi) ∨
      ((¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi) ∨
      (¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2187 chi ∧
      ¬PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom2258 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi) ∨
      ((¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi) ∨
      (¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2187 chi ∧
      ¬PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom2261 chi))) ∨
      ((¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2187 chi ∧
      ¬PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom2262 chi) ∨
      ((¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom2263 chi) ∨
      (¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom2266 chi) ∨
      ((¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom2267 chi) ∨
      (¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi))) ∨
      ((¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom2269 chi) ∨
      ((¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi) ∨
      (¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom2271 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) ∨
      ((¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2011 chi ∧
      ¬PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom2223 chi ∧
      ¬PredecessorHalfFin13Atom2273 chi) ∨
      (¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2274 chi))) ∨
      ((¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) ∨
      ((¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2011 chi ∧
      ¬PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom2277 chi) ∨
      (¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom2278 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi) ∨
      ((¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom2034 chi ∧
      ¬PredecessorHalfFin13Atom2209 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom2230 chi ∧
      ¬PredecessorHalfFin13Atom2280 chi) ∨
      (¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2213 chi ∧
      ¬PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom2231 chi ∧
      ¬PredecessorHalfFin13Atom2281 chi))) ∨
      ((¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2216 chi ∧
      ¬PredecessorHalfFin13Atom2217 chi ∧
      ¬PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom2282 chi) ∨
      ((¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2228 chi ∧
      ¬PredecessorHalfFin13Atom2283 chi) ∨
      (¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom2036 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2226 chi ∧
      ¬PredecessorHalfFin13Atom2227 chi ∧
      ¬PredecessorHalfFin13Atom2232 chi ∧
      ¬PredecessorHalfFin13Atom2287 chi) ∨
      ((¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) ∨
      (¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom2254 chi ∧
      ¬PredecessorHalfFin13Atom2269 chi))) ∨
      ((¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi) ∨
      ((¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom2256 chi ∧
      ¬PredecessorHalfFin13Atom2271 chi) ∨
      (¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2011 chi ∧
      ¬PredecessorHalfFin13Atom2017 chi ∧
      ¬PredecessorHalfFin13Atom2027 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom2248 chi ∧
      ¬PredecessorHalfFin13Atom2258 chi ∧
      ¬PredecessorHalfFin13Atom2273 chi) ∨
      ((¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom2259 chi ∧
      ¬PredecessorHalfFin13Atom2274 chi) ∨
      (¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi))) ∨
      (((¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2011 chi ∧
      ¬PredecessorHalfFin13Atom2020 chi ∧
      ¬PredecessorHalfFin13Atom2030 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom2251 chi ∧
      ¬PredecessorHalfFin13Atom2261 chi ∧
      ¬PredecessorHalfFin13Atom2276 chi) ∨
      (¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2011 chi ∧
      ¬PredecessorHalfFin13Atom2021 chi ∧
      ¬PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom2240 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2242 chi ∧
      ¬PredecessorHalfFin13Atom2252 chi ∧
      ¬PredecessorHalfFin13Atom2262 chi ∧
      ¬PredecessorHalfFin13Atom2277 chi)) ∨
      ((¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2013 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2032 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2244 chi ∧
      ¬PredecessorHalfFin13Atom2246 chi ∧
      ¬PredecessorHalfFin13Atom2249 chi ∧
      ¬PredecessorHalfFin13Atom2263 chi ∧
      ¬PredecessorHalfFin13Atom2278 chi) ∨
      (¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi))))))))) := by
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
              exact predecessorHalfFin13_clause28062 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28063 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28065 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28066 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28067 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28068 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28069 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28070 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28071 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28072 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28074 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28075 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28077 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28078 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28079 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28081 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28082 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28083 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28084 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28085 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28086 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28089 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28090 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28091 chi hno hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28092 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28093 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28094 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28095 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28096 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28097 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28098 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28101 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28105 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28106 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28107 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28108 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28109 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28111 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28112 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28113 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28114 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28115 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28116 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28117 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28118 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28119 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28121 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28122 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28123 chi hno hbad
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
              exact predecessorHalfFin13_clause28124 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28125 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28126 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28127 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28128 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28129 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28131 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28132 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28133 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28134 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28135 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28136 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28137 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28138 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28139 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28140 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28141 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28142 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28144 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28145 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28146 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28147 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28148 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28149 chi hno hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28150 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28151 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28152 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28153 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28155 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28156 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28157 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28158 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28159 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28160 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28161 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28162 chi hno hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28165 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28167 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28168 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28169 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28170 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28171 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause28172 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28173 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28174 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28175 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28176 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause28177 chi hno hbad
              ·
                exact predecessorHalfFin13_clause28178 chi hno hbad

end ErdosSzekeres

end
