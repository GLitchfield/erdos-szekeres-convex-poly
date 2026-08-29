module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 097. -/

theorem predecessorHalfFin13_clause28096 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1877 chi ∧
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
      ¬PredecessorHalfFin13Atom2274 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 6, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3788
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1879
    PredecessorHalfFin13Atom1885 PredecessorHalfFin13Atom1886 PredecessorHalfFin13Atom1888
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1896 PredecessorHalfFin13Atom1898
    PredecessorHalfFin13Atom1907 PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2007
    PredecessorHalfFin13Atom2009 PredecessorHalfFin13Atom2018 PredecessorHalfFin13Atom2028
    PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2133 PredecessorHalfFin13Atom2135
    PredecessorHalfFin13Atom2144 PredecessorHalfFin13Atom2154 PredecessorHalfFin13Atom2274 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28097 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1877 chi ∧
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
      ¬PredecessorHalfFin13Atom2275 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5836
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1880
    PredecessorHalfFin13Atom1885 PredecessorHalfFin13Atom1887 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1899
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2008
    PredecessorHalfFin13Atom2010 PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2029
    PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2134 PredecessorHalfFin13Atom2136
    PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2275 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28098 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1877 chi ∧
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
      ¬PredecessorHalfFin13Atom2276 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 6, 7, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6860
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1879 PredecessorHalfFin13Atom1880
    PredecessorHalfFin13Atom1886 PredecessorHalfFin13Atom1887 PredecessorHalfFin13Atom1890
    PredecessorHalfFin13Atom1896 PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1900
    PredecessorHalfFin13Atom1909 PredecessorHalfFin13Atom2007 PredecessorHalfFin13Atom2008
    PredecessorHalfFin13Atom2011 PredecessorHalfFin13Atom2020 PredecessorHalfFin13Atom2030
    PredecessorHalfFin13Atom2133 PredecessorHalfFin13Atom2134 PredecessorHalfFin13Atom2137
    PredecessorHalfFin13Atom2146 PredecessorHalfFin13Atom2156 PredecessorHalfFin13Atom2276 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28101 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1881 chi ∧
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
      ¬PredecessorHalfFin13Atom2279 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5964
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1884
    PredecessorHalfFin13Atom1885 PredecessorHalfFin13Atom1887 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1905
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2014
    PredecessorHalfFin13Atom2016 PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2140 PredecessorHalfFin13Atom2142
    PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2159 PredecessorHalfFin13Atom2279 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28105 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1891 chi ∧
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
      ¬PredecessorHalfFin13Atom2283 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 7, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3980
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1893
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1896 PredecessorHalfFin13Atom1898
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1902 PredecessorHalfFin13Atom1904
    PredecessorHalfFin13Atom1907 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2023
    PredecessorHalfFin13Atom2025 PredecessorHalfFin13Atom2028 PredecessorHalfFin13Atom2032
    PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2149 PredecessorHalfFin13Atom2151
    PredecessorHalfFin13Atom2154 PredecessorHalfFin13Atom2158 PredecessorHalfFin13Atom2283 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28106 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1891 chi ∧
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
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6028
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1894
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1899
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1905
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2026 PredecessorHalfFin13Atom2029 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2150 PredecessorHalfFin13Atom2152
    PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2159 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28107 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1891 chi ∧
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
      ¬PredecessorHalfFin13Atom2285 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 7, 8, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7052
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1893 PredecessorHalfFin13Atom1894
    PredecessorHalfFin13Atom1896 PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1900
    PredecessorHalfFin13Atom1902 PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1906
    PredecessorHalfFin13Atom1909 PredecessorHalfFin13Atom2023 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2027 PredecessorHalfFin13Atom2030 PredecessorHalfFin13Atom2034
    PredecessorHalfFin13Atom2149 PredecessorHalfFin13Atom2150 PredecessorHalfFin13Atom2153
    PredecessorHalfFin13Atom2156 PredecessorHalfFin13Atom2160 PredecessorHalfFin13Atom2285 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28108 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1892 chi ∧
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
      ¬PredecessorHalfFin13Atom2286 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 7, 8, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7564
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1893 PredecessorHalfFin13Atom1894
    PredecessorHalfFin13Atom1898 PredecessorHalfFin13Atom1899 PredecessorHalfFin13Atom1900
    PredecessorHalfFin13Atom1904 PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom1906
    PredecessorHalfFin13Atom1910 PredecessorHalfFin13Atom2025 PredecessorHalfFin13Atom2026
    PredecessorHalfFin13Atom2027 PredecessorHalfFin13Atom2031 PredecessorHalfFin13Atom2035
    PredecessorHalfFin13Atom2151 PredecessorHalfFin13Atom2152 PredecessorHalfFin13Atom2153
    PredecessorHalfFin13Atom2157 PredecessorHalfFin13Atom2161 PredecessorHalfFin13Atom2286 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28109 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1895 chi ∧
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
      ¬PredecessorHalfFin13Atom2287 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 7, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7820
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1896 PredecessorHalfFin13Atom1897
    PredecessorHalfFin13Atom1898 PredecessorHalfFin13Atom1899 PredecessorHalfFin13Atom1900
    PredecessorHalfFin13Atom1907 PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom1909
    PredecessorHalfFin13Atom1910 PredecessorHalfFin13Atom2028 PredecessorHalfFin13Atom2029
    PredecessorHalfFin13Atom2030 PredecessorHalfFin13Atom2031 PredecessorHalfFin13Atom2036
    PredecessorHalfFin13Atom2154 PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2156
    PredecessorHalfFin13Atom2157 PredecessorHalfFin13Atom2162 PredecessorHalfFin13Atom2287 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28111 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1911 chi ∧
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
      ¬PredecessorHalfFin13Atom2233 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1012
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1913
    PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1922
    PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1937
    PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1968
    PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom2002
    PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2168
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2233 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28112 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1911 chi ∧
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
      ¬PredecessorHalfFin13Atom2234 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1524
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1914
    PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1923
    PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1938
    PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1969
    PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom2003
    PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2169
    PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2234 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28113 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1911 chi ∧
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
      ¬PredecessorHalfFin13Atom2235 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 7, 8, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2548
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1915
    PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1920 PredecessorHalfFin13Atom1924
    PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1935 PredecessorHalfFin13Atom1939
    PredecessorHalfFin13Atom1949 PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1970
    PredecessorHalfFin13Atom1974 PredecessorHalfFin13Atom1984 PredecessorHalfFin13Atom2004
    PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2166 PredecessorHalfFin13Atom2170
    PredecessorHalfFin13Atom2180 PredecessorHalfFin13Atom2200 PredecessorHalfFin13Atom2235 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28114 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1911 chi ∧
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
      ¬PredecessorHalfFin13Atom2236 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4596
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1921 PredecessorHalfFin13Atom1925
    PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1936 PredecessorHalfFin13Atom1940
    PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1975 PredecessorHalfFin13Atom1985 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2167 PredecessorHalfFin13Atom2171
    PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2201 PredecessorHalfFin13Atom2236 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28115 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1911 chi ∧
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
      ¬PredecessorHalfFin13Atom2237 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1780
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1914
    PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1926
    PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1941
    PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1969
    PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom2006
    PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2172
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2237 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28116 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1911 chi ∧
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
      ¬PredecessorHalfFin13Atom2238 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 7, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2804
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1915
    PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1920 PredecessorHalfFin13Atom1927
    PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1935 PredecessorHalfFin13Atom1942
    PredecessorHalfFin13Atom1952 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1970
    PredecessorHalfFin13Atom1977 PredecessorHalfFin13Atom1987 PredecessorHalfFin13Atom2007
    PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2166 PredecessorHalfFin13Atom2173
    PredecessorHalfFin13Atom2183 PredecessorHalfFin13Atom2203 PredecessorHalfFin13Atom2238 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28117 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1911 chi ∧
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
      ¬PredecessorHalfFin13Atom2239 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4852
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1921 PredecessorHalfFin13Atom1928
    PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1936 PredecessorHalfFin13Atom1943
    PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1978 PredecessorHalfFin13Atom1988 PredecessorHalfFin13Atom2008
    PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2167 PredecessorHalfFin13Atom2174
    PredecessorHalfFin13Atom2184 PredecessorHalfFin13Atom2204 PredecessorHalfFin13Atom2239 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28118 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1911 chi ∧
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
      ¬PredecessorHalfFin13Atom2240 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 7, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3316
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1915
    PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1920 PredecessorHalfFin13Atom1929
    PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1935 PredecessorHalfFin13Atom1944
    PredecessorHalfFin13Atom1954 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1970
    PredecessorHalfFin13Atom1979 PredecessorHalfFin13Atom1989 PredecessorHalfFin13Atom2009
    PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2166 PredecessorHalfFin13Atom2175
    PredecessorHalfFin13Atom2185 PredecessorHalfFin13Atom2205 PredecessorHalfFin13Atom2240 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28119 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1911 chi ∧
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
      ¬PredecessorHalfFin13Atom2241 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5364
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1921 PredecessorHalfFin13Atom1930
    PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1936 PredecessorHalfFin13Atom1945
    PredecessorHalfFin13Atom1955 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1980 PredecessorHalfFin13Atom1990 PredecessorHalfFin13Atom2010
    PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2167 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2186 PredecessorHalfFin13Atom2206 PredecessorHalfFin13Atom2241 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28121 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1912 chi ∧
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
      ¬PredecessorHalfFin13Atom2243 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1908
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1914
    PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1926
    PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1941
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1973
    PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom2012
    PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2172
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2243 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28122 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1912 chi ∧
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
      ¬PredecessorHalfFin13Atom2244 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2932
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1915
    PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1924 PredecessorHalfFin13Atom1927
    PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1939 PredecessorHalfFin13Atom1942
    PredecessorHalfFin13Atom1958 PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1974
    PredecessorHalfFin13Atom1977 PredecessorHalfFin13Atom1993 PredecessorHalfFin13Atom2013
    PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2170 PredecessorHalfFin13Atom2173
    PredecessorHalfFin13Atom2189 PredecessorHalfFin13Atom2209 PredecessorHalfFin13Atom2244 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28123 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1912 chi ∧
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
      ¬PredecessorHalfFin13Atom2245 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4980
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1925 PredecessorHalfFin13Atom1928
    PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom1943
    PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1975
    PredecessorHalfFin13Atom1978 PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom2014
    PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2171 PredecessorHalfFin13Atom2174
    PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2245 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28124 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1912 chi ∧
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
      ¬PredecessorHalfFin13Atom2246 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3444
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1915
    PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1924 PredecessorHalfFin13Atom1929
    PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1939 PredecessorHalfFin13Atom1944
    PredecessorHalfFin13Atom1960 PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1974
    PredecessorHalfFin13Atom1979 PredecessorHalfFin13Atom1995 PredecessorHalfFin13Atom2015
    PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2170 PredecessorHalfFin13Atom2175
    PredecessorHalfFin13Atom2191 PredecessorHalfFin13Atom2211 PredecessorHalfFin13Atom2246 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28125 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1912 chi ∧
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
      ¬PredecessorHalfFin13Atom2247 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5492
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1925 PredecessorHalfFin13Atom1930
    PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom1945
    PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1975
    PredecessorHalfFin13Atom1980 PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom2016
    PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2171 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2192 PredecessorHalfFin13Atom2212 PredecessorHalfFin13Atom2247 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28126 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1912 chi ∧
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
      ¬PredecessorHalfFin13Atom2248 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 8, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6516
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1915 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1924 PredecessorHalfFin13Atom1925 PredecessorHalfFin13Atom1931
    PredecessorHalfFin13Atom1939 PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom1946
    PredecessorHalfFin13Atom1962 PredecessorHalfFin13Atom1974 PredecessorHalfFin13Atom1975
    PredecessorHalfFin13Atom1981 PredecessorHalfFin13Atom1997 PredecessorHalfFin13Atom2017
    PredecessorHalfFin13Atom2170 PredecessorHalfFin13Atom2171 PredecessorHalfFin13Atom2177
    PredecessorHalfFin13Atom2193 PredecessorHalfFin13Atom2213 PredecessorHalfFin13Atom2248 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28127 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1913 chi ∧
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
      ¬PredecessorHalfFin13Atom2249 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3700
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1915
    PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1927 PredecessorHalfFin13Atom1929
    PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1942 PredecessorHalfFin13Atom1944
    PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1977
    PredecessorHalfFin13Atom1979 PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom2018
    PredecessorHalfFin13Atom2172 PredecessorHalfFin13Atom2173 PredecessorHalfFin13Atom2175
    PredecessorHalfFin13Atom2194 PredecessorHalfFin13Atom2214 PredecessorHalfFin13Atom2249 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28128 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1913 chi ∧
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
      ¬PredecessorHalfFin13Atom2250 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5748
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1928 PredecessorHalfFin13Atom1930
    PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1943 PredecessorHalfFin13Atom1945
    PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1978
    PredecessorHalfFin13Atom1980 PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2019
    PredecessorHalfFin13Atom2172 PredecessorHalfFin13Atom2174 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2250 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28129 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1913 chi ∧
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
      ¬PredecessorHalfFin13Atom2251 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 6, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6772
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1915 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1927 PredecessorHalfFin13Atom1928 PredecessorHalfFin13Atom1931
    PredecessorHalfFin13Atom1942 PredecessorHalfFin13Atom1943 PredecessorHalfFin13Atom1946
    PredecessorHalfFin13Atom1965 PredecessorHalfFin13Atom1977 PredecessorHalfFin13Atom1978
    PredecessorHalfFin13Atom1981 PredecessorHalfFin13Atom2000 PredecessorHalfFin13Atom2020
    PredecessorHalfFin13Atom2173 PredecessorHalfFin13Atom2174 PredecessorHalfFin13Atom2177
    PredecessorHalfFin13Atom2196 PredecessorHalfFin13Atom2216 PredecessorHalfFin13Atom2251 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28131 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1917 chi ∧
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
      ¬PredecessorHalfFin13Atom2253 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1972
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1919
    PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1926
    PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1951
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1983
    PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom2022
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2182
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2253 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28132 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1917 chi ∧
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
      ¬PredecessorHalfFin13Atom2254 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2996
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1920
    PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1924 PredecessorHalfFin13Atom1927
    PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1949 PredecessorHalfFin13Atom1952
    PredecessorHalfFin13Atom1958 PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1984
    PredecessorHalfFin13Atom1987 PredecessorHalfFin13Atom1993 PredecessorHalfFin13Atom2023
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2180 PredecessorHalfFin13Atom2183
    PredecessorHalfFin13Atom2189 PredecessorHalfFin13Atom2219 PredecessorHalfFin13Atom2254 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28133 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1917 chi ∧
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
      ¬PredecessorHalfFin13Atom2255 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5044
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1921
    PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1925 PredecessorHalfFin13Atom1928
    PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom1953
    PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1985
    PredecessorHalfFin13Atom1988 PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2184
    PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2220 PredecessorHalfFin13Atom2255 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28134 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1917 chi ∧
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
      ¬PredecessorHalfFin13Atom2256 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3508
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1920
    PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1924 PredecessorHalfFin13Atom1929
    PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1949 PredecessorHalfFin13Atom1954
    PredecessorHalfFin13Atom1960 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom1984
    PredecessorHalfFin13Atom1989 PredecessorHalfFin13Atom1995 PredecessorHalfFin13Atom2025
    PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2180 PredecessorHalfFin13Atom2185
    PredecessorHalfFin13Atom2191 PredecessorHalfFin13Atom2221 PredecessorHalfFin13Atom2256 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28135 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1917 chi ∧
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
      ¬PredecessorHalfFin13Atom2257 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5556
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1921
    PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1925 PredecessorHalfFin13Atom1930
    PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom1955
    PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom1985
    PredecessorHalfFin13Atom1990 PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom2026
    PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2186
    PredecessorHalfFin13Atom2192 PredecessorHalfFin13Atom2222 PredecessorHalfFin13Atom2257 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28136 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1917 chi ∧
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
      ¬PredecessorHalfFin13Atom2258 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 8, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6580
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1920 PredecessorHalfFin13Atom1921
    PredecessorHalfFin13Atom1924 PredecessorHalfFin13Atom1925 PredecessorHalfFin13Atom1931
    PredecessorHalfFin13Atom1949 PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom1956
    PredecessorHalfFin13Atom1962 PredecessorHalfFin13Atom1984 PredecessorHalfFin13Atom1985
    PredecessorHalfFin13Atom1991 PredecessorHalfFin13Atom1997 PredecessorHalfFin13Atom2027
    PredecessorHalfFin13Atom2180 PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2187
    PredecessorHalfFin13Atom2193 PredecessorHalfFin13Atom2223 PredecessorHalfFin13Atom2258 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28137 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1918 chi ∧
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
      ¬PredecessorHalfFin13Atom2259 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3764
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1920
    PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1927 PredecessorHalfFin13Atom1929
    PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1952 PredecessorHalfFin13Atom1954
    PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1987
    PredecessorHalfFin13Atom1989 PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom2028
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2183 PredecessorHalfFin13Atom2185
    PredecessorHalfFin13Atom2194 PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2259 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28138 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1918 chi ∧
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
      ¬PredecessorHalfFin13Atom2260 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5812
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1921
    PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1928 PredecessorHalfFin13Atom1930
    PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom1955
    PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1988
    PredecessorHalfFin13Atom1990 PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2029
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2184 PredecessorHalfFin13Atom2186
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2260 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28139 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1918 chi ∧
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
      ¬PredecessorHalfFin13Atom2261 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6836
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1920 PredecessorHalfFin13Atom1921
    PredecessorHalfFin13Atom1927 PredecessorHalfFin13Atom1928 PredecessorHalfFin13Atom1931
    PredecessorHalfFin13Atom1952 PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom1956
    PredecessorHalfFin13Atom1965 PredecessorHalfFin13Atom1987 PredecessorHalfFin13Atom1988
    PredecessorHalfFin13Atom1991 PredecessorHalfFin13Atom2000 PredecessorHalfFin13Atom2030
    PredecessorHalfFin13Atom2183 PredecessorHalfFin13Atom2184 PredecessorHalfFin13Atom2187
    PredecessorHalfFin13Atom2196 PredecessorHalfFin13Atom2226 PredecessorHalfFin13Atom2261 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28140 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1919 chi ∧
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
      ¬PredecessorHalfFin13Atom2262 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 7, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7348
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1920 PredecessorHalfFin13Atom1921
    PredecessorHalfFin13Atom1929 PredecessorHalfFin13Atom1930 PredecessorHalfFin13Atom1931
    PredecessorHalfFin13Atom1954 PredecessorHalfFin13Atom1955 PredecessorHalfFin13Atom1956
    PredecessorHalfFin13Atom1966 PredecessorHalfFin13Atom1989 PredecessorHalfFin13Atom1990
    PredecessorHalfFin13Atom1991 PredecessorHalfFin13Atom2001 PredecessorHalfFin13Atom2031
    PredecessorHalfFin13Atom2185 PredecessorHalfFin13Atom2186 PredecessorHalfFin13Atom2187
    PredecessorHalfFin13Atom2197 PredecessorHalfFin13Atom2227 PredecessorHalfFin13Atom2262 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28141 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1922 chi ∧
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
      ¬PredecessorHalfFin13Atom2263 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3892
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1924
    PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1927 PredecessorHalfFin13Atom1929
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1958 PredecessorHalfFin13Atom1960
    PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom1993
    PredecessorHalfFin13Atom1995 PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom2032
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2189 PredecessorHalfFin13Atom2191
    PredecessorHalfFin13Atom2194 PredecessorHalfFin13Atom2228 PredecessorHalfFin13Atom2263 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28142 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1922 chi ∧
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
      ¬PredecessorHalfFin13Atom2264 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5940
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1925
    PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1928 PredecessorHalfFin13Atom1930
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom1961
    PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom1994
    PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2192
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2229 PredecessorHalfFin13Atom2264 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28144 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1923 chi ∧
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
      ¬PredecessorHalfFin13Atom2266 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 8, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7476
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1924 PredecessorHalfFin13Atom1925
    PredecessorHalfFin13Atom1929 PredecessorHalfFin13Atom1930 PredecessorHalfFin13Atom1931
    PredecessorHalfFin13Atom1960 PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom1962
    PredecessorHalfFin13Atom1966 PredecessorHalfFin13Atom1995 PredecessorHalfFin13Atom1996
    PredecessorHalfFin13Atom1997 PredecessorHalfFin13Atom2001 PredecessorHalfFin13Atom2035
    PredecessorHalfFin13Atom2191 PredecessorHalfFin13Atom2192 PredecessorHalfFin13Atom2193
    PredecessorHalfFin13Atom2197 PredecessorHalfFin13Atom2231 PredecessorHalfFin13Atom2266 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28145 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1926 chi ∧
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
      ¬PredecessorHalfFin13Atom2267 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 5, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7732
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1927 PredecessorHalfFin13Atom1928
    PredecessorHalfFin13Atom1929 PredecessorHalfFin13Atom1930 PredecessorHalfFin13Atom1931
    PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom1965
    PredecessorHalfFin13Atom1966 PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom1999
    PredecessorHalfFin13Atom2000 PredecessorHalfFin13Atom2001 PredecessorHalfFin13Atom2036
    PredecessorHalfFin13Atom2194 PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2196
    PredecessorHalfFin13Atom2197 PredecessorHalfFin13Atom2232 PredecessorHalfFin13Atom2267 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28146 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1932 chi ∧
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
      ¬PredecessorHalfFin13Atom2268 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2004
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1934
    PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1941
    PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1951
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2003
    PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2022
    PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2202
    PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2268 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28147 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1932 chi ∧
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
      ¬PredecessorHalfFin13Atom2269 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 7, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3028
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1935
    PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1939 PredecessorHalfFin13Atom1942
    PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1949 PredecessorHalfFin13Atom1952
    PredecessorHalfFin13Atom1958 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2004
    PredecessorHalfFin13Atom2007 PredecessorHalfFin13Atom2013 PredecessorHalfFin13Atom2023
    PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2200 PredecessorHalfFin13Atom2203
    PredecessorHalfFin13Atom2209 PredecessorHalfFin13Atom2219 PredecessorHalfFin13Atom2269 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28148 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1932 chi ∧
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
      ¬PredecessorHalfFin13Atom2270 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5076
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1936
    PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom1943
    PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom1953
    PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2008 PredecessorHalfFin13Atom2014 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2201 PredecessorHalfFin13Atom2204
    PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2220 PredecessorHalfFin13Atom2270 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28149 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1932 chi ∧
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
      ¬PredecessorHalfFin13Atom2271 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 7, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3540
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1935
    PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1939 PredecessorHalfFin13Atom1944
    PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1949 PredecessorHalfFin13Atom1954
    PredecessorHalfFin13Atom1960 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2004
    PredecessorHalfFin13Atom2009 PredecessorHalfFin13Atom2015 PredecessorHalfFin13Atom2025
    PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2200 PredecessorHalfFin13Atom2205
    PredecessorHalfFin13Atom2211 PredecessorHalfFin13Atom2221 PredecessorHalfFin13Atom2271 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28150 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1932 chi ∧
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
      ¬PredecessorHalfFin13Atom2272 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5588
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1936
    PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom1945
    PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom1955
    PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2010 PredecessorHalfFin13Atom2016 PredecessorHalfFin13Atom2026
    PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2201 PredecessorHalfFin13Atom2206
    PredecessorHalfFin13Atom2212 PredecessorHalfFin13Atom2222 PredecessorHalfFin13Atom2272 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28151 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1932 chi ∧
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
      ¬PredecessorHalfFin13Atom2273 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 7, 8, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6612
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1935 PredecessorHalfFin13Atom1936
    PredecessorHalfFin13Atom1939 PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom1946
    PredecessorHalfFin13Atom1949 PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom1956
    PredecessorHalfFin13Atom1962 PredecessorHalfFin13Atom2004 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2011 PredecessorHalfFin13Atom2017 PredecessorHalfFin13Atom2027
    PredecessorHalfFin13Atom2200 PredecessorHalfFin13Atom2201 PredecessorHalfFin13Atom2207
    PredecessorHalfFin13Atom2213 PredecessorHalfFin13Atom2223 PredecessorHalfFin13Atom2273 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28152 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1933 chi ∧
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
      ¬PredecessorHalfFin13Atom2274 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3796
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1935
    PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1942 PredecessorHalfFin13Atom1944
    PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1952 PredecessorHalfFin13Atom1954
    PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2007
    PredecessorHalfFin13Atom2009 PredecessorHalfFin13Atom2018 PredecessorHalfFin13Atom2028
    PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2203 PredecessorHalfFin13Atom2205
    PredecessorHalfFin13Atom2214 PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2274 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28153 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1933 chi ∧
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
      ¬PredecessorHalfFin13Atom2275 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5844
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1936
    PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1943 PredecessorHalfFin13Atom1945
    PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom1955
    PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2008
    PredecessorHalfFin13Atom2010 PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2029
    PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2204 PredecessorHalfFin13Atom2206
    PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2275 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28155 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1934 chi ∧
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
      ¬PredecessorHalfFin13Atom2277 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 7, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7380
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1935 PredecessorHalfFin13Atom1936
    PredecessorHalfFin13Atom1944 PredecessorHalfFin13Atom1945 PredecessorHalfFin13Atom1946
    PredecessorHalfFin13Atom1954 PredecessorHalfFin13Atom1955 PredecessorHalfFin13Atom1956
    PredecessorHalfFin13Atom1966 PredecessorHalfFin13Atom2009 PredecessorHalfFin13Atom2010
    PredecessorHalfFin13Atom2011 PredecessorHalfFin13Atom2021 PredecessorHalfFin13Atom2031
    PredecessorHalfFin13Atom2205 PredecessorHalfFin13Atom2206 PredecessorHalfFin13Atom2207
    PredecessorHalfFin13Atom2217 PredecessorHalfFin13Atom2227 PredecessorHalfFin13Atom2277 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28156 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1937 chi ∧
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
      ¬PredecessorHalfFin13Atom2278 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3924
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1939
    PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1942 PredecessorHalfFin13Atom1944
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1958 PredecessorHalfFin13Atom1960
    PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2013
    PredecessorHalfFin13Atom2015 PredecessorHalfFin13Atom2018 PredecessorHalfFin13Atom2032
    PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2209 PredecessorHalfFin13Atom2211
    PredecessorHalfFin13Atom2214 PredecessorHalfFin13Atom2228 PredecessorHalfFin13Atom2278 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28157 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1937 chi ∧
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
      ¬PredecessorHalfFin13Atom2279 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5972
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1940
    PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1943 PredecessorHalfFin13Atom1945
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom1961
    PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2014
    PredecessorHalfFin13Atom2016 PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2212
    PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2229 PredecessorHalfFin13Atom2279 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28158 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1937 chi ∧
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
      ¬PredecessorHalfFin13Atom2280 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 8, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6996
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1939 PredecessorHalfFin13Atom1940
    PredecessorHalfFin13Atom1942 PredecessorHalfFin13Atom1943 PredecessorHalfFin13Atom1946
    PredecessorHalfFin13Atom1958 PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom1962
    PredecessorHalfFin13Atom1965 PredecessorHalfFin13Atom2013 PredecessorHalfFin13Atom2014
    PredecessorHalfFin13Atom2017 PredecessorHalfFin13Atom2020 PredecessorHalfFin13Atom2034
    PredecessorHalfFin13Atom2209 PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2213
    PredecessorHalfFin13Atom2216 PredecessorHalfFin13Atom2230 PredecessorHalfFin13Atom2280 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28159 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1938 chi ∧
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
      ¬PredecessorHalfFin13Atom2281 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 8, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7508
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1939 PredecessorHalfFin13Atom1940
    PredecessorHalfFin13Atom1944 PredecessorHalfFin13Atom1945 PredecessorHalfFin13Atom1946
    PredecessorHalfFin13Atom1960 PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom1962
    PredecessorHalfFin13Atom1966 PredecessorHalfFin13Atom2015 PredecessorHalfFin13Atom2016
    PredecessorHalfFin13Atom2017 PredecessorHalfFin13Atom2021 PredecessorHalfFin13Atom2035
    PredecessorHalfFin13Atom2211 PredecessorHalfFin13Atom2212 PredecessorHalfFin13Atom2213
    PredecessorHalfFin13Atom2217 PredecessorHalfFin13Atom2231 PredecessorHalfFin13Atom2281 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28160 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1941 chi ∧
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
      ¬PredecessorHalfFin13Atom2282 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 6, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7764
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1942 PredecessorHalfFin13Atom1943
    PredecessorHalfFin13Atom1944 PredecessorHalfFin13Atom1945 PredecessorHalfFin13Atom1946
    PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom1965
    PredecessorHalfFin13Atom1966 PredecessorHalfFin13Atom2018 PredecessorHalfFin13Atom2019
    PredecessorHalfFin13Atom2020 PredecessorHalfFin13Atom2021 PredecessorHalfFin13Atom2036
    PredecessorHalfFin13Atom2214 PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2216
    PredecessorHalfFin13Atom2217 PredecessorHalfFin13Atom2232 PredecessorHalfFin13Atom2282 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28161 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1947 chi ∧
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
      ¬PredecessorHalfFin13Atom2283 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 7, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3988
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1949
    PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1952 PredecessorHalfFin13Atom1954
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1958 PredecessorHalfFin13Atom1960
    PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2023
    PredecessorHalfFin13Atom2025 PredecessorHalfFin13Atom2028 PredecessorHalfFin13Atom2032
    PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2219 PredecessorHalfFin13Atom2221
    PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2228 PredecessorHalfFin13Atom2283 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28162 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1947 chi ∧
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
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6036
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1950
    PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom1955
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom1961
    PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2026 PredecessorHalfFin13Atom2029 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2220 PredecessorHalfFin13Atom2222
    PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2229 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28165 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1951 chi ∧
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
      ¬PredecessorHalfFin13Atom2287 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 4, 7, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7828
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1952 PredecessorHalfFin13Atom1953
    PredecessorHalfFin13Atom1954 PredecessorHalfFin13Atom1955 PredecessorHalfFin13Atom1956
    PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom1965
    PredecessorHalfFin13Atom1966 PredecessorHalfFin13Atom2028 PredecessorHalfFin13Atom2029
    PredecessorHalfFin13Atom2030 PredecessorHalfFin13Atom2031 PredecessorHalfFin13Atom2036
    PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2226
    PredecessorHalfFin13Atom2227 PredecessorHalfFin13Atom2232 PredecessorHalfFin13Atom2287 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28167 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1967 chi ∧
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
      ¬PredecessorHalfFin13Atom2268 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2020
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1969
    PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1976
    PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom1986
    PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2003
    PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2022
    PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2237
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2268 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28168 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1967 chi ∧
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
      ¬PredecessorHalfFin13Atom2269 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 7, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3044
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1970
    PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1974 PredecessorHalfFin13Atom1977
    PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1984 PredecessorHalfFin13Atom1987
    PredecessorHalfFin13Atom1993 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2004
    PredecessorHalfFin13Atom2007 PredecessorHalfFin13Atom2013 PredecessorHalfFin13Atom2023
    PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2235 PredecessorHalfFin13Atom2238
    PredecessorHalfFin13Atom2244 PredecessorHalfFin13Atom2254 PredecessorHalfFin13Atom2269 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28169 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1967 chi ∧
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
      ¬PredecessorHalfFin13Atom2270 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5092
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1975 PredecessorHalfFin13Atom1978
    PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1985 PredecessorHalfFin13Atom1988
    PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2008 PredecessorHalfFin13Atom2014 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2236 PredecessorHalfFin13Atom2239
    PredecessorHalfFin13Atom2245 PredecessorHalfFin13Atom2255 PredecessorHalfFin13Atom2270 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28170 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1967 chi ∧
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
      ¬PredecessorHalfFin13Atom2271 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 7, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3556
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1970
    PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1974 PredecessorHalfFin13Atom1979
    PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom1984 PredecessorHalfFin13Atom1989
    PredecessorHalfFin13Atom1995 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2004
    PredecessorHalfFin13Atom2009 PredecessorHalfFin13Atom2015 PredecessorHalfFin13Atom2025
    PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2235 PredecessorHalfFin13Atom2240
    PredecessorHalfFin13Atom2246 PredecessorHalfFin13Atom2256 PredecessorHalfFin13Atom2271 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28171 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1967 chi ∧
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
      ¬PredecessorHalfFin13Atom2272 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5604
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1975 PredecessorHalfFin13Atom1980
    PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom1985 PredecessorHalfFin13Atom1990
    PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2010 PredecessorHalfFin13Atom2016 PredecessorHalfFin13Atom2026
    PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2236 PredecessorHalfFin13Atom2241
    PredecessorHalfFin13Atom2247 PredecessorHalfFin13Atom2257 PredecessorHalfFin13Atom2272 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28172 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1967 chi ∧
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
      ¬PredecessorHalfFin13Atom2273 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 7, 8, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6628
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1970 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1974 PredecessorHalfFin13Atom1975 PredecessorHalfFin13Atom1981
    PredecessorHalfFin13Atom1984 PredecessorHalfFin13Atom1985 PredecessorHalfFin13Atom1991
    PredecessorHalfFin13Atom1997 PredecessorHalfFin13Atom2004 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2011 PredecessorHalfFin13Atom2017 PredecessorHalfFin13Atom2027
    PredecessorHalfFin13Atom2235 PredecessorHalfFin13Atom2236 PredecessorHalfFin13Atom2242
    PredecessorHalfFin13Atom2248 PredecessorHalfFin13Atom2258 PredecessorHalfFin13Atom2273 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28173 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1968 chi ∧
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
      ¬PredecessorHalfFin13Atom2274 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3812
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1970
    PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1977 PredecessorHalfFin13Atom1979
    PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1987 PredecessorHalfFin13Atom1989
    PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2007
    PredecessorHalfFin13Atom2009 PredecessorHalfFin13Atom2018 PredecessorHalfFin13Atom2028
    PredecessorHalfFin13Atom2237 PredecessorHalfFin13Atom2238 PredecessorHalfFin13Atom2240
    PredecessorHalfFin13Atom2249 PredecessorHalfFin13Atom2259 PredecessorHalfFin13Atom2274 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28174 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1968 chi ∧
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
      ¬PredecessorHalfFin13Atom2275 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5860
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1978 PredecessorHalfFin13Atom1980
    PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1988 PredecessorHalfFin13Atom1990
    PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2008
    PredecessorHalfFin13Atom2010 PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2029
    PredecessorHalfFin13Atom2237 PredecessorHalfFin13Atom2239 PredecessorHalfFin13Atom2241
    PredecessorHalfFin13Atom2250 PredecessorHalfFin13Atom2260 PredecessorHalfFin13Atom2275 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28175 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1968 chi ∧
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
      ¬PredecessorHalfFin13Atom2276 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 7, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6884
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1970 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1977 PredecessorHalfFin13Atom1978 PredecessorHalfFin13Atom1981
    PredecessorHalfFin13Atom1987 PredecessorHalfFin13Atom1988 PredecessorHalfFin13Atom1991
    PredecessorHalfFin13Atom2000 PredecessorHalfFin13Atom2007 PredecessorHalfFin13Atom2008
    PredecessorHalfFin13Atom2011 PredecessorHalfFin13Atom2020 PredecessorHalfFin13Atom2030
    PredecessorHalfFin13Atom2238 PredecessorHalfFin13Atom2239 PredecessorHalfFin13Atom2242
    PredecessorHalfFin13Atom2251 PredecessorHalfFin13Atom2261 PredecessorHalfFin13Atom2276 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28176 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1969 chi ∧
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
      ¬PredecessorHalfFin13Atom2277 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 7, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7396
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1970 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1979 PredecessorHalfFin13Atom1980 PredecessorHalfFin13Atom1981
    PredecessorHalfFin13Atom1989 PredecessorHalfFin13Atom1990 PredecessorHalfFin13Atom1991
    PredecessorHalfFin13Atom2001 PredecessorHalfFin13Atom2009 PredecessorHalfFin13Atom2010
    PredecessorHalfFin13Atom2011 PredecessorHalfFin13Atom2021 PredecessorHalfFin13Atom2031
    PredecessorHalfFin13Atom2240 PredecessorHalfFin13Atom2241 PredecessorHalfFin13Atom2242
    PredecessorHalfFin13Atom2252 PredecessorHalfFin13Atom2262 PredecessorHalfFin13Atom2277 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28177 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1972 chi ∧
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
      ¬PredecessorHalfFin13Atom2278 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3940
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1974
    PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1977 PredecessorHalfFin13Atom1979
    PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom1993 PredecessorHalfFin13Atom1995
    PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2013
    PredecessorHalfFin13Atom2015 PredecessorHalfFin13Atom2018 PredecessorHalfFin13Atom2032
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2244 PredecessorHalfFin13Atom2246
    PredecessorHalfFin13Atom2249 PredecessorHalfFin13Atom2263 PredecessorHalfFin13Atom2278 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28178 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1972 chi ∧
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
      ¬PredecessorHalfFin13Atom2279 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5988
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1975
    PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1978 PredecessorHalfFin13Atom1980
    PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom1996
    PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2014
    PredecessorHalfFin13Atom2016 PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2245 PredecessorHalfFin13Atom2247
    PredecessorHalfFin13Atom2250 PredecessorHalfFin13Atom2264 PredecessorHalfFin13Atom2279 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28180 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1973 chi ∧
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
      ¬PredecessorHalfFin13Atom2281 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 6, 8, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7524
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1974 PredecessorHalfFin13Atom1975
    PredecessorHalfFin13Atom1979 PredecessorHalfFin13Atom1980 PredecessorHalfFin13Atom1981
    PredecessorHalfFin13Atom1995 PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom1997
    PredecessorHalfFin13Atom2001 PredecessorHalfFin13Atom2015 PredecessorHalfFin13Atom2016
    PredecessorHalfFin13Atom2017 PredecessorHalfFin13Atom2021 PredecessorHalfFin13Atom2035
    PredecessorHalfFin13Atom2246 PredecessorHalfFin13Atom2247 PredecessorHalfFin13Atom2248
    PredecessorHalfFin13Atom2252 PredecessorHalfFin13Atom2266 PredecessorHalfFin13Atom2281 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28182 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1982 chi ∧
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
      ¬PredecessorHalfFin13Atom2283 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 7, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4004
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom1984
    PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1987 PredecessorHalfFin13Atom1989
    PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom1993 PredecessorHalfFin13Atom1995
    PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2023
    PredecessorHalfFin13Atom2025 PredecessorHalfFin13Atom2028 PredecessorHalfFin13Atom2032
    PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2254 PredecessorHalfFin13Atom2256
    PredecessorHalfFin13Atom2259 PredecessorHalfFin13Atom2263 PredecessorHalfFin13Atom2283 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28183 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1982 chi ∧
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
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6052
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom1985
    PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1988 PredecessorHalfFin13Atom1990
    PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom1996
    PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2026 PredecessorHalfFin13Atom2029 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2255 PredecessorHalfFin13Atom2257
    PredecessorHalfFin13Atom2260 PredecessorHalfFin13Atom2264 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28186 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1986 chi ∧
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
      ¬PredecessorHalfFin13Atom2287 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 5, 7, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7844
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1987 PredecessorHalfFin13Atom1988
    PredecessorHalfFin13Atom1989 PredecessorHalfFin13Atom1990 PredecessorHalfFin13Atom1991
    PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2000
    PredecessorHalfFin13Atom2001 PredecessorHalfFin13Atom2028 PredecessorHalfFin13Atom2029
    PredecessorHalfFin13Atom2030 PredecessorHalfFin13Atom2031 PredecessorHalfFin13Atom2036
    PredecessorHalfFin13Atom2259 PredecessorHalfFin13Atom2260 PredecessorHalfFin13Atom2261
    PredecessorHalfFin13Atom2262 PredecessorHalfFin13Atom2267 PredecessorHalfFin13Atom2287 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28188 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2002 chi ∧
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
      ¬PredecessorHalfFin13Atom2283 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 6, 7, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4036
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2004
    PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2007 PredecessorHalfFin13Atom2009
    PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2013 PredecessorHalfFin13Atom2015
    PredecessorHalfFin13Atom2018 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2023
    PredecessorHalfFin13Atom2025 PredecessorHalfFin13Atom2028 PredecessorHalfFin13Atom2032
    PredecessorHalfFin13Atom2268 PredecessorHalfFin13Atom2269 PredecessorHalfFin13Atom2271
    PredecessorHalfFin13Atom2274 PredecessorHalfFin13Atom2278 PredecessorHalfFin13Atom2283 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28189 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2002 chi ∧
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
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 6, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6084
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2008 PredecessorHalfFin13Atom2010
    PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2014 PredecessorHalfFin13Atom2016
    PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2026 PredecessorHalfFin13Atom2029 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2268 PredecessorHalfFin13Atom2270 PredecessorHalfFin13Atom2272
    PredecessorHalfFin13Atom2275 PredecessorHalfFin13Atom2279 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28193 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2012 chi ∧
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
      ¬PredecessorHalfFin13Atom2288 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 6, 8, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask8004
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2013 PredecessorHalfFin13Atom2014
    PredecessorHalfFin13Atom2015 PredecessorHalfFin13Atom2016 PredecessorHalfFin13Atom2017
    PredecessorHalfFin13Atom2018 PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2020
    PredecessorHalfFin13Atom2021 PredecessorHalfFin13Atom2032 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2034 PredecessorHalfFin13Atom2035 PredecessorHalfFin13Atom2036
    PredecessorHalfFin13Atom2278 PredecessorHalfFin13Atom2279 PredecessorHalfFin13Atom2280
    PredecessorHalfFin13Atom2281 PredecessorHalfFin13Atom2282 PredecessorHalfFin13Atom2288 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28194 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2022 chi ∧
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
      ¬PredecessorHalfFin13Atom2288 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 7, 8, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask8068
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2023 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2025 PredecessorHalfFin13Atom2026 PredecessorHalfFin13Atom2027
    PredecessorHalfFin13Atom2028 PredecessorHalfFin13Atom2029 PredecessorHalfFin13Atom2030
    PredecessorHalfFin13Atom2031 PredecessorHalfFin13Atom2032 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2034 PredecessorHalfFin13Atom2035 PredecessorHalfFin13Atom2036
    PredecessorHalfFin13Atom2283 PredecessorHalfFin13Atom2284 PredecessorHalfFin13Atom2285
    PredecessorHalfFin13Atom2286 PredecessorHalfFin13Atom2287 PredecessorHalfFin13Atom2288 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28195 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2037 chi ∧
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
      ¬PredecessorHalfFin13Atom2233 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1016
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2039
    PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2048
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2063
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2094
    PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2128
    PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2168
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2233 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28196 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2037 chi ∧
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
      ¬PredecessorHalfFin13Atom2234 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1528
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2040
    PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2049
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2064
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2095
    PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2129
    PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2169
    PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2234 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28197 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2037 chi ∧
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
      ¬PredecessorHalfFin13Atom2235 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 7, 8, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2552
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2041
    PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2046 PredecessorHalfFin13Atom2050
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2061 PredecessorHalfFin13Atom2065
    PredecessorHalfFin13Atom2075 PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2096
    PredecessorHalfFin13Atom2100 PredecessorHalfFin13Atom2110 PredecessorHalfFin13Atom2130
    PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2166 PredecessorHalfFin13Atom2170
    PredecessorHalfFin13Atom2180 PredecessorHalfFin13Atom2200 PredecessorHalfFin13Atom2235 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28198 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2037 chi ∧
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
      ¬PredecessorHalfFin13Atom2236 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4600
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2042
    PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2047 PredecessorHalfFin13Atom2051
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2062 PredecessorHalfFin13Atom2066
    PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2097
    PredecessorHalfFin13Atom2101 PredecessorHalfFin13Atom2111 PredecessorHalfFin13Atom2131
    PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2167 PredecessorHalfFin13Atom2171
    PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2201 PredecessorHalfFin13Atom2236 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28199 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2037 chi ∧
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
      ¬PredecessorHalfFin13Atom2237 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1784
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2040
    PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2052
    PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2067
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2095
    PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2132
    PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2172
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2237 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28200 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2037 chi ∧
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
      ¬PredecessorHalfFin13Atom2238 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 7, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2808
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2041
    PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2046 PredecessorHalfFin13Atom2053
    PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2061 PredecessorHalfFin13Atom2068
    PredecessorHalfFin13Atom2078 PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2096
    PredecessorHalfFin13Atom2103 PredecessorHalfFin13Atom2113 PredecessorHalfFin13Atom2133
    PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2166 PredecessorHalfFin13Atom2173
    PredecessorHalfFin13Atom2183 PredecessorHalfFin13Atom2203 PredecessorHalfFin13Atom2238 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28201 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2037 chi ∧
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
      ¬PredecessorHalfFin13Atom2239 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4856
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2042
    PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2047 PredecessorHalfFin13Atom2054
    PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2062 PredecessorHalfFin13Atom2069
    PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2097
    PredecessorHalfFin13Atom2104 PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2134
    PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2167 PredecessorHalfFin13Atom2174
    PredecessorHalfFin13Atom2184 PredecessorHalfFin13Atom2204 PredecessorHalfFin13Atom2239 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28202 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2037 chi ∧
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
      ¬PredecessorHalfFin13Atom2240 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 7, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3320
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2041
    PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2046 PredecessorHalfFin13Atom2055
    PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2061 PredecessorHalfFin13Atom2070
    PredecessorHalfFin13Atom2080 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2096
    PredecessorHalfFin13Atom2105 PredecessorHalfFin13Atom2115 PredecessorHalfFin13Atom2135
    PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2166 PredecessorHalfFin13Atom2175
    PredecessorHalfFin13Atom2185 PredecessorHalfFin13Atom2205 PredecessorHalfFin13Atom2240 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28203 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2037 chi ∧
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
      ¬PredecessorHalfFin13Atom2241 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5368
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2042
    PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2047 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2062 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2081 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2097
    PredecessorHalfFin13Atom2106 PredecessorHalfFin13Atom2116 PredecessorHalfFin13Atom2136
    PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2167 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2186 PredecessorHalfFin13Atom2206 PredecessorHalfFin13Atom2241 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28205 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2038 chi ∧
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
      ¬PredecessorHalfFin13Atom2243 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1912
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2040
    PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2052
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2067
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2099
    PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2138
    PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2172
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2243 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28206 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2038 chi ∧
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
      ¬PredecessorHalfFin13Atom2244 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2936
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2041
    PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2050 PredecessorHalfFin13Atom2053
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2065 PredecessorHalfFin13Atom2068
    PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2100
    PredecessorHalfFin13Atom2103 PredecessorHalfFin13Atom2119 PredecessorHalfFin13Atom2139
    PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2170 PredecessorHalfFin13Atom2173
    PredecessorHalfFin13Atom2189 PredecessorHalfFin13Atom2209 PredecessorHalfFin13Atom2244 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28207 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2038 chi ∧
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
      ¬PredecessorHalfFin13Atom2245 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4984
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2042
    PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2051 PredecessorHalfFin13Atom2054
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2066 PredecessorHalfFin13Atom2069
    PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2101
    PredecessorHalfFin13Atom2104 PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2140
    PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2171 PredecessorHalfFin13Atom2174
    PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2245 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28208 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2038 chi ∧
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
      ¬PredecessorHalfFin13Atom2246 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3448
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2041
    PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2050 PredecessorHalfFin13Atom2055
    PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2065 PredecessorHalfFin13Atom2070
    PredecessorHalfFin13Atom2086 PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2100
    PredecessorHalfFin13Atom2105 PredecessorHalfFin13Atom2121 PredecessorHalfFin13Atom2141
    PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2170 PredecessorHalfFin13Atom2175
    PredecessorHalfFin13Atom2191 PredecessorHalfFin13Atom2211 PredecessorHalfFin13Atom2246 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28209 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2038 chi ∧
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
      ¬PredecessorHalfFin13Atom2247 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5496
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2042
    PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2051 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2066 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2101
    PredecessorHalfFin13Atom2106 PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2142
    PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2171 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2192 PredecessorHalfFin13Atom2212 PredecessorHalfFin13Atom2247 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28211 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2039 chi ∧
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
      ¬PredecessorHalfFin13Atom2249 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3704
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2041
    PredecessorHalfFin13Atom2052 PredecessorHalfFin13Atom2053 PredecessorHalfFin13Atom2055
    PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2068 PredecessorHalfFin13Atom2070
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2103
    PredecessorHalfFin13Atom2105 PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2144
    PredecessorHalfFin13Atom2172 PredecessorHalfFin13Atom2173 PredecessorHalfFin13Atom2175
    PredecessorHalfFin13Atom2194 PredecessorHalfFin13Atom2214 PredecessorHalfFin13Atom2249 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28212 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2039 chi ∧
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
      ¬PredecessorHalfFin13Atom2250 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5752
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2042
    PredecessorHalfFin13Atom2052 PredecessorHalfFin13Atom2054 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2069 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2104
    PredecessorHalfFin13Atom2106 PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2145
    PredecessorHalfFin13Atom2172 PredecessorHalfFin13Atom2174 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2250 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28213 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2039 chi ∧
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
      ¬PredecessorHalfFin13Atom2251 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6776
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2041 PredecessorHalfFin13Atom2042
    PredecessorHalfFin13Atom2053 PredecessorHalfFin13Atom2054 PredecessorHalfFin13Atom2057
    PredecessorHalfFin13Atom2068 PredecessorHalfFin13Atom2069 PredecessorHalfFin13Atom2072
    PredecessorHalfFin13Atom2091 PredecessorHalfFin13Atom2103 PredecessorHalfFin13Atom2104
    PredecessorHalfFin13Atom2107 PredecessorHalfFin13Atom2126 PredecessorHalfFin13Atom2146
    PredecessorHalfFin13Atom2173 PredecessorHalfFin13Atom2174 PredecessorHalfFin13Atom2177
    PredecessorHalfFin13Atom2196 PredecessorHalfFin13Atom2216 PredecessorHalfFin13Atom2251 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28214 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2040 chi ∧
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
      ¬PredecessorHalfFin13Atom2252 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 6, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7288
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2041 PredecessorHalfFin13Atom2042
    PredecessorHalfFin13Atom2055 PredecessorHalfFin13Atom2056 PredecessorHalfFin13Atom2057
    PredecessorHalfFin13Atom2070 PredecessorHalfFin13Atom2071 PredecessorHalfFin13Atom2072
    PredecessorHalfFin13Atom2092 PredecessorHalfFin13Atom2105 PredecessorHalfFin13Atom2106
    PredecessorHalfFin13Atom2107 PredecessorHalfFin13Atom2127 PredecessorHalfFin13Atom2147
    PredecessorHalfFin13Atom2175 PredecessorHalfFin13Atom2176 PredecessorHalfFin13Atom2177
    PredecessorHalfFin13Atom2197 PredecessorHalfFin13Atom2217 PredecessorHalfFin13Atom2252 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28215 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2043 chi ∧
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
      ¬PredecessorHalfFin13Atom2253 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1976
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2045
    PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2052
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2077
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2109
    PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2148
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2182
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2253 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28216 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2043 chi ∧
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
      ¬PredecessorHalfFin13Atom2254 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 7, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3000
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2046
    PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2050 PredecessorHalfFin13Atom2053
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2075 PredecessorHalfFin13Atom2078
    PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2110
    PredecessorHalfFin13Atom2113 PredecessorHalfFin13Atom2119 PredecessorHalfFin13Atom2149
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2180 PredecessorHalfFin13Atom2183
    PredecessorHalfFin13Atom2189 PredecessorHalfFin13Atom2219 PredecessorHalfFin13Atom2254 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28217 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2043 chi ∧
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
      ¬PredecessorHalfFin13Atom2255 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5048
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2047
    PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2051 PredecessorHalfFin13Atom2054
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2079
    PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2111
    PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2150
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2184
    PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2220 PredecessorHalfFin13Atom2255 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28218 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2043 chi ∧
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
      ¬PredecessorHalfFin13Atom2256 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 7, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3512
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2046
    PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2050 PredecessorHalfFin13Atom2055
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2075 PredecessorHalfFin13Atom2080
    PredecessorHalfFin13Atom2086 PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2110
    PredecessorHalfFin13Atom2115 PredecessorHalfFin13Atom2121 PredecessorHalfFin13Atom2151
    PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2180 PredecessorHalfFin13Atom2185
    PredecessorHalfFin13Atom2191 PredecessorHalfFin13Atom2221 PredecessorHalfFin13Atom2256 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28219 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2043 chi ∧
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
      ¬PredecessorHalfFin13Atom2257 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5560
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2047
    PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2051 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2081
    PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2111
    PredecessorHalfFin13Atom2116 PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2152
    PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2186
    PredecessorHalfFin13Atom2192 PredecessorHalfFin13Atom2222 PredecessorHalfFin13Atom2257 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28221 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2044 chi ∧
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
      ¬PredecessorHalfFin13Atom2259 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3768
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2046
    PredecessorHalfFin13Atom2052 PredecessorHalfFin13Atom2053 PredecessorHalfFin13Atom2055
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2078 PredecessorHalfFin13Atom2080
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2113
    PredecessorHalfFin13Atom2115 PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2154
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2183 PredecessorHalfFin13Atom2185
    PredecessorHalfFin13Atom2194 PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2259 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28222 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2044 chi ∧
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
      ¬PredecessorHalfFin13Atom2260 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5816
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2047
    PredecessorHalfFin13Atom2052 PredecessorHalfFin13Atom2054 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2081
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2114
    PredecessorHalfFin13Atom2116 PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2155
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2184 PredecessorHalfFin13Atom2186
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2260 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28223 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2044 chi ∧
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
      ¬PredecessorHalfFin13Atom2261 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 7, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6840
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2046 PredecessorHalfFin13Atom2047
    PredecessorHalfFin13Atom2053 PredecessorHalfFin13Atom2054 PredecessorHalfFin13Atom2057
    PredecessorHalfFin13Atom2078 PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2082
    PredecessorHalfFin13Atom2091 PredecessorHalfFin13Atom2113 PredecessorHalfFin13Atom2114
    PredecessorHalfFin13Atom2117 PredecessorHalfFin13Atom2126 PredecessorHalfFin13Atom2156
    PredecessorHalfFin13Atom2183 PredecessorHalfFin13Atom2184 PredecessorHalfFin13Atom2187
    PredecessorHalfFin13Atom2196 PredecessorHalfFin13Atom2226 PredecessorHalfFin13Atom2261 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28225 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2048 chi ∧
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
      ¬PredecessorHalfFin13Atom2263 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3896
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2050
    PredecessorHalfFin13Atom2052 PredecessorHalfFin13Atom2053 PredecessorHalfFin13Atom2055
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2086
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2119
    PredecessorHalfFin13Atom2121 PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2158
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2189 PredecessorHalfFin13Atom2191
    PredecessorHalfFin13Atom2194 PredecessorHalfFin13Atom2228 PredecessorHalfFin13Atom2263 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28226 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2048 chi ∧
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
      ¬PredecessorHalfFin13Atom2264 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5944
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2051
    PredecessorHalfFin13Atom2052 PredecessorHalfFin13Atom2054 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2087
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2120
    PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2159
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2192
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2229 PredecessorHalfFin13Atom2264 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28227 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2048 chi ∧
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
      ¬PredecessorHalfFin13Atom2265 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 8, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6968
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2050 PredecessorHalfFin13Atom2051
    PredecessorHalfFin13Atom2053 PredecessorHalfFin13Atom2054 PredecessorHalfFin13Atom2057
    PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2088
    PredecessorHalfFin13Atom2091 PredecessorHalfFin13Atom2119 PredecessorHalfFin13Atom2120
    PredecessorHalfFin13Atom2123 PredecessorHalfFin13Atom2126 PredecessorHalfFin13Atom2160
    PredecessorHalfFin13Atom2189 PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2193
    PredecessorHalfFin13Atom2196 PredecessorHalfFin13Atom2230 PredecessorHalfFin13Atom2265 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28229 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2052 chi ∧
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
      ¬PredecessorHalfFin13Atom2267 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 5, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7736
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2052 PredecessorHalfFin13Atom2053 PredecessorHalfFin13Atom2054
    PredecessorHalfFin13Atom2055 PredecessorHalfFin13Atom2056 PredecessorHalfFin13Atom2057
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2091
    PredecessorHalfFin13Atom2092 PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2125
    PredecessorHalfFin13Atom2126 PredecessorHalfFin13Atom2127 PredecessorHalfFin13Atom2162
    PredecessorHalfFin13Atom2194 PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2196
    PredecessorHalfFin13Atom2197 PredecessorHalfFin13Atom2232 PredecessorHalfFin13Atom2267 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28230 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2058 chi ∧
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
      ¬PredecessorHalfFin13Atom2268 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2008
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2060
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2067
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2077
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2129
    PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2148
    PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2202
    PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2268 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28231 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2058 chi ∧
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
      ¬PredecessorHalfFin13Atom2269 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 7, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3032
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2061
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2065 PredecessorHalfFin13Atom2068
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2075 PredecessorHalfFin13Atom2078
    PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2130
    PredecessorHalfFin13Atom2133 PredecessorHalfFin13Atom2139 PredecessorHalfFin13Atom2149
    PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2200 PredecessorHalfFin13Atom2203
    PredecessorHalfFin13Atom2209 PredecessorHalfFin13Atom2219 PredecessorHalfFin13Atom2269 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28232 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2058 chi ∧
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
      ¬PredecessorHalfFin13Atom2270 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5080
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2062
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2066 PredecessorHalfFin13Atom2069
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2079
    PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2131
    PredecessorHalfFin13Atom2134 PredecessorHalfFin13Atom2140 PredecessorHalfFin13Atom2150
    PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2201 PredecessorHalfFin13Atom2204
    PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2220 PredecessorHalfFin13Atom2270 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28233 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2058 chi ∧
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
      ¬PredecessorHalfFin13Atom2271 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 7, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3544
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2061
    PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2065 PredecessorHalfFin13Atom2070
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2075 PredecessorHalfFin13Atom2080
    PredecessorHalfFin13Atom2086 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2130
    PredecessorHalfFin13Atom2135 PredecessorHalfFin13Atom2141 PredecessorHalfFin13Atom2151
    PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2200 PredecessorHalfFin13Atom2205
    PredecessorHalfFin13Atom2211 PredecessorHalfFin13Atom2221 PredecessorHalfFin13Atom2271 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28234 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2058 chi ∧
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
      ¬PredecessorHalfFin13Atom2272 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5592
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2062
    PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2066 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2081
    PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2131
    PredecessorHalfFin13Atom2136 PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2152
    PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2201 PredecessorHalfFin13Atom2206
    PredecessorHalfFin13Atom2212 PredecessorHalfFin13Atom2222 PredecessorHalfFin13Atom2272 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28235 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2058 chi ∧
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
      ¬PredecessorHalfFin13Atom2273 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 7, 8, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6616
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2061 PredecessorHalfFin13Atom2062
    PredecessorHalfFin13Atom2065 PredecessorHalfFin13Atom2066 PredecessorHalfFin13Atom2072
    PredecessorHalfFin13Atom2075 PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2082
    PredecessorHalfFin13Atom2088 PredecessorHalfFin13Atom2130 PredecessorHalfFin13Atom2131
    PredecessorHalfFin13Atom2137 PredecessorHalfFin13Atom2143 PredecessorHalfFin13Atom2153
    PredecessorHalfFin13Atom2200 PredecessorHalfFin13Atom2201 PredecessorHalfFin13Atom2207
    PredecessorHalfFin13Atom2213 PredecessorHalfFin13Atom2223 PredecessorHalfFin13Atom2273 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28236 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2059 chi ∧
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
      ¬PredecessorHalfFin13Atom2274 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3800
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2061
    PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2068 PredecessorHalfFin13Atom2070
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2078 PredecessorHalfFin13Atom2080
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2133
    PredecessorHalfFin13Atom2135 PredecessorHalfFin13Atom2144 PredecessorHalfFin13Atom2154
    PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2203 PredecessorHalfFin13Atom2205
    PredecessorHalfFin13Atom2214 PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2274 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28237 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2059 chi ∧
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
      ¬PredecessorHalfFin13Atom2275 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5848
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2062
    PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2069 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2081
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2134
    PredecessorHalfFin13Atom2136 PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2155
    PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2204 PredecessorHalfFin13Atom2206
    PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2275 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28238 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2059 chi ∧
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
      ¬PredecessorHalfFin13Atom2276 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 7, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6872
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2061 PredecessorHalfFin13Atom2062
    PredecessorHalfFin13Atom2068 PredecessorHalfFin13Atom2069 PredecessorHalfFin13Atom2072
    PredecessorHalfFin13Atom2078 PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2082
    PredecessorHalfFin13Atom2091 PredecessorHalfFin13Atom2133 PredecessorHalfFin13Atom2134
    PredecessorHalfFin13Atom2137 PredecessorHalfFin13Atom2146 PredecessorHalfFin13Atom2156
    PredecessorHalfFin13Atom2203 PredecessorHalfFin13Atom2204 PredecessorHalfFin13Atom2207
    PredecessorHalfFin13Atom2216 PredecessorHalfFin13Atom2226 PredecessorHalfFin13Atom2276 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28239 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2060 chi ∧
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
      ¬PredecessorHalfFin13Atom2277 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 7, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7384
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2061 PredecessorHalfFin13Atom2062
    PredecessorHalfFin13Atom2070 PredecessorHalfFin13Atom2071 PredecessorHalfFin13Atom2072
    PredecessorHalfFin13Atom2080 PredecessorHalfFin13Atom2081 PredecessorHalfFin13Atom2082
    PredecessorHalfFin13Atom2092 PredecessorHalfFin13Atom2135 PredecessorHalfFin13Atom2136
    PredecessorHalfFin13Atom2137 PredecessorHalfFin13Atom2147 PredecessorHalfFin13Atom2157
    PredecessorHalfFin13Atom2205 PredecessorHalfFin13Atom2206 PredecessorHalfFin13Atom2207
    PredecessorHalfFin13Atom2217 PredecessorHalfFin13Atom2227 PredecessorHalfFin13Atom2277 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28240 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2063 chi ∧
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
      ¬PredecessorHalfFin13Atom2278 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3928
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2065
    PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2068 PredecessorHalfFin13Atom2070
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2086
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2139
    PredecessorHalfFin13Atom2141 PredecessorHalfFin13Atom2144 PredecessorHalfFin13Atom2158
    PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2209 PredecessorHalfFin13Atom2211
    PredecessorHalfFin13Atom2214 PredecessorHalfFin13Atom2228 PredecessorHalfFin13Atom2278 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28241 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2063 chi ∧
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
      ¬PredecessorHalfFin13Atom2279 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5976
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2066
    PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2069 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2087
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2140
    PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2159
    PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2212
    PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2229 PredecessorHalfFin13Atom2279 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28242 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2063 chi ∧
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
      ¬PredecessorHalfFin13Atom2280 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 8, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7000
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2065 PredecessorHalfFin13Atom2066
    PredecessorHalfFin13Atom2068 PredecessorHalfFin13Atom2069 PredecessorHalfFin13Atom2072
    PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2088
    PredecessorHalfFin13Atom2091 PredecessorHalfFin13Atom2139 PredecessorHalfFin13Atom2140
    PredecessorHalfFin13Atom2143 PredecessorHalfFin13Atom2146 PredecessorHalfFin13Atom2160
    PredecessorHalfFin13Atom2209 PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2213
    PredecessorHalfFin13Atom2216 PredecessorHalfFin13Atom2230 PredecessorHalfFin13Atom2280 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28243 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2064 chi ∧
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
      ¬PredecessorHalfFin13Atom2281 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 8, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7512
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2065 PredecessorHalfFin13Atom2066
    PredecessorHalfFin13Atom2070 PredecessorHalfFin13Atom2071 PredecessorHalfFin13Atom2072
    PredecessorHalfFin13Atom2086 PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2088
    PredecessorHalfFin13Atom2092 PredecessorHalfFin13Atom2141 PredecessorHalfFin13Atom2142
    PredecessorHalfFin13Atom2143 PredecessorHalfFin13Atom2147 PredecessorHalfFin13Atom2161
    PredecessorHalfFin13Atom2211 PredecessorHalfFin13Atom2212 PredecessorHalfFin13Atom2213
    PredecessorHalfFin13Atom2217 PredecessorHalfFin13Atom2231 PredecessorHalfFin13Atom2281 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28244 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2067 chi ∧
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
      ¬PredecessorHalfFin13Atom2282 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 6, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7768
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2068 PredecessorHalfFin13Atom2069
    PredecessorHalfFin13Atom2070 PredecessorHalfFin13Atom2071 PredecessorHalfFin13Atom2072
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2091
    PredecessorHalfFin13Atom2092 PredecessorHalfFin13Atom2144 PredecessorHalfFin13Atom2145
    PredecessorHalfFin13Atom2146 PredecessorHalfFin13Atom2147 PredecessorHalfFin13Atom2162
    PredecessorHalfFin13Atom2214 PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2216
    PredecessorHalfFin13Atom2217 PredecessorHalfFin13Atom2232 PredecessorHalfFin13Atom2282 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28245 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2073 chi ∧
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
      ¬PredecessorHalfFin13Atom2283 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 7, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3992
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2075
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2078 PredecessorHalfFin13Atom2080
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2086
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2149
    PredecessorHalfFin13Atom2151 PredecessorHalfFin13Atom2154 PredecessorHalfFin13Atom2158
    PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2219 PredecessorHalfFin13Atom2221
    PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2228 PredecessorHalfFin13Atom2283 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28246 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2073 chi ∧
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
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6040
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2076
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2081
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2087
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2150
    PredecessorHalfFin13Atom2152 PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2159
    PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2220 PredecessorHalfFin13Atom2222
    PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2229 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28247 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2073 chi ∧
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
      ¬PredecessorHalfFin13Atom2285 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 7, 8, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7064
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2075 PredecessorHalfFin13Atom2076
    PredecessorHalfFin13Atom2078 PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2082
    PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2088
    PredecessorHalfFin13Atom2091 PredecessorHalfFin13Atom2149 PredecessorHalfFin13Atom2150
    PredecessorHalfFin13Atom2153 PredecessorHalfFin13Atom2156 PredecessorHalfFin13Atom2160
    PredecessorHalfFin13Atom2219 PredecessorHalfFin13Atom2220 PredecessorHalfFin13Atom2223
    PredecessorHalfFin13Atom2226 PredecessorHalfFin13Atom2230 PredecessorHalfFin13Atom2285 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28249 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2077 chi ∧
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
      ¬PredecessorHalfFin13Atom2287 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 7, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7832
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2078 PredecessorHalfFin13Atom2079
    PredecessorHalfFin13Atom2080 PredecessorHalfFin13Atom2081 PredecessorHalfFin13Atom2082
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2091
    PredecessorHalfFin13Atom2092 PredecessorHalfFin13Atom2154 PredecessorHalfFin13Atom2155
    PredecessorHalfFin13Atom2156 PredecessorHalfFin13Atom2157 PredecessorHalfFin13Atom2162
    PredecessorHalfFin13Atom2224 PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2226
    PredecessorHalfFin13Atom2227 PredecessorHalfFin13Atom2232 PredecessorHalfFin13Atom2287 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28250 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom2083 chi ∧
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
      ¬PredecessorHalfFin13Atom2288 chi) := by
  intro hbad
  apply hno
  refine ⟨{3, 4, 8, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7960
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2085
    PredecessorHalfFin13Atom2086 PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2088
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2091
    PredecessorHalfFin13Atom2092 PredecessorHalfFin13Atom2158 PredecessorHalfFin13Atom2159
    PredecessorHalfFin13Atom2160 PredecessorHalfFin13Atom2161 PredecessorHalfFin13Atom2162
    PredecessorHalfFin13Atom2228 PredecessorHalfFin13Atom2229 PredecessorHalfFin13Atom2230
    PredecessorHalfFin13Atom2231 PredecessorHalfFin13Atom2232 PredecessorHalfFin13Atom2288 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

end ErdosSzekeres

end
