module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 095. -/

theorem predecessorHalfFin13_clause27138 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4781
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1181
    PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1192 PredecessorHalfFin13Atom1199
    PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1241 PredecessorHalfFin13Atom1248
    PredecessorHalfFin13Atom1273 PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1325
    PredecessorHalfFin13Atom1332 PredecessorHalfFin13Atom1357 PredecessorHalfFin13Atom1448
    PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1865 PredecessorHalfFin13Atom1872
    PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1988 PredecessorHalfFin13Atom2114 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27140 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5293
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1176 PredecessorHalfFin13Atom1179 PredecessorHalfFin13Atom1181
    PredecessorHalfFin13Atom1190 PredecessorHalfFin13Atom1192 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1241 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1275 PredecessorHalfFin13Atom1323 PredecessorHalfFin13Atom1325
    PredecessorHalfFin13Atom1334 PredecessorHalfFin13Atom1359 PredecessorHalfFin13Atom1450
    PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1865 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1899 PredecessorHalfFin13Atom1990 PredecessorHalfFin13Atom2116 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27142 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1837
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1179
    PredecessorHalfFin13Atom1193 PredecessorHalfFin13Atom1194 PredecessorHalfFin13Atom1197
    PredecessorHalfFin13Atom1242 PredecessorHalfFin13Atom1243 PredecessorHalfFin13Atom1246
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1327
    PredecessorHalfFin13Atom1330 PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1452
    PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1870
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom2118 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27144 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4909
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1181
    PredecessorHalfFin13Atom1193 PredecessorHalfFin13Atom1196 PredecessorHalfFin13Atom1199
    PredecessorHalfFin13Atom1242 PredecessorHalfFin13Atom1245 PredecessorHalfFin13Atom1248
    PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1329
    PredecessorHalfFin13Atom1332 PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1454
    PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1869 PredecessorHalfFin13Atom1872
    PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom2120 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27146 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5421
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1177 PredecessorHalfFin13Atom1179 PredecessorHalfFin13Atom1181
    PredecessorHalfFin13Atom1194 PredecessorHalfFin13Atom1196 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1243 PredecessorHalfFin13Atom1245 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1281 PredecessorHalfFin13Atom1327 PredecessorHalfFin13Atom1329
    PredecessorHalfFin13Atom1334 PredecessorHalfFin13Atom1365 PredecessorHalfFin13Atom1456
    PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1869 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom2122 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27149 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 5, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5677
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1178 PredecessorHalfFin13Atom1179 PredecessorHalfFin13Atom1181
    PredecessorHalfFin13Atom1197 PredecessorHalfFin13Atom1199 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1246 PredecessorHalfFin13Atom1248 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1330 PredecessorHalfFin13Atom1332
    PredecessorHalfFin13Atom1334 PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1459
    PredecessorHalfFin13Atom1870 PredecessorHalfFin13Atom1872 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2125 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27152 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0973
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1184
    PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1193
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1257
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1337
    PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1462
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1881
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2128 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27153 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 6, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1485
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1185
    PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1190 PredecessorHalfFin13Atom1194
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1258
    PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1338
    PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1463
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1882
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2129 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27155 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 6, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4557
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1187
    PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1192 PredecessorHalfFin13Atom1196
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1260
    PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1340
    PredecessorHalfFin13Atom1344 PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1884
    PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom2005 PredecessorHalfFin13Atom2131 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27156 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1741
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1185
    PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1190 PredecessorHalfFin13Atom1197
    PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1261
    PredecessorHalfFin13Atom1271 PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1338
    PredecessorHalfFin13Atom1345 PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1466
    PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1885
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2132 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27158 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4813
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1187
    PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1192 PredecessorHalfFin13Atom1199
    PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1263
    PredecessorHalfFin13Atom1273 PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1340
    PredecessorHalfFin13Atom1347 PredecessorHalfFin13Atom1357 PredecessorHalfFin13Atom1468
    PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1887
    PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom2008 PredecessorHalfFin13Atom2134 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27160 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5325
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1182 PredecessorHalfFin13Atom1185 PredecessorHalfFin13Atom1187
    PredecessorHalfFin13Atom1190 PredecessorHalfFin13Atom1192 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1275 PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1340
    PredecessorHalfFin13Atom1349 PredecessorHalfFin13Atom1359 PredecessorHalfFin13Atom1470
    PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1899 PredecessorHalfFin13Atom2010 PredecessorHalfFin13Atom2136 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27162 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 6, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1869
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1185
    PredecessorHalfFin13Atom1193 PredecessorHalfFin13Atom1194 PredecessorHalfFin13Atom1197
    PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1261
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1342
    PredecessorHalfFin13Atom1345 PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1472
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1885
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2138 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27164 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 6, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4941
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1187
    PredecessorHalfFin13Atom1193 PredecessorHalfFin13Atom1196 PredecessorHalfFin13Atom1199
    PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1260 PredecessorHalfFin13Atom1263
    PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1344
    PredecessorHalfFin13Atom1347 PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1474
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1887
    PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom2014 PredecessorHalfFin13Atom2140 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27166 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5453
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1183 PredecessorHalfFin13Atom1185 PredecessorHalfFin13Atom1187
    PredecessorHalfFin13Atom1194 PredecessorHalfFin13Atom1196 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1260 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1281 PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1344
    PredecessorHalfFin13Atom1349 PredecessorHalfFin13Atom1365 PredecessorHalfFin13Atom1476
    PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom2016 PredecessorHalfFin13Atom2142 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27169 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5709
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1184 PredecessorHalfFin13Atom1185 PredecessorHalfFin13Atom1187
    PredecessorHalfFin13Atom1197 PredecessorHalfFin13Atom1199 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1261 PredecessorHalfFin13Atom1263 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1345 PredecessorHalfFin13Atom1347
    PredecessorHalfFin13Atom1349 PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1479
    PredecessorHalfFin13Atom1885 PredecessorHalfFin13Atom1887 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2145 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27172 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1933
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1190
    PredecessorHalfFin13Atom1193 PredecessorHalfFin13Atom1194 PredecessorHalfFin13Atom1197
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1271
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1352
    PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1482
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1895
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2148 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27174 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5005
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1192
    PredecessorHalfFin13Atom1193 PredecessorHalfFin13Atom1196 PredecessorHalfFin13Atom1199
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1273
    PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1354
    PredecessorHalfFin13Atom1357 PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1897
    PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom2024 PredecessorHalfFin13Atom2150 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27176 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5517
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1188 PredecessorHalfFin13Atom1190 PredecessorHalfFin13Atom1192
    PredecessorHalfFin13Atom1194 PredecessorHalfFin13Atom1196 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1275
    PredecessorHalfFin13Atom1281 PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1354
    PredecessorHalfFin13Atom1359 PredecessorHalfFin13Atom1365 PredecessorHalfFin13Atom1486
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1899
    PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom2026 PredecessorHalfFin13Atom2152 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27179 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5773
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1189 PredecessorHalfFin13Atom1190 PredecessorHalfFin13Atom1192
    PredecessorHalfFin13Atom1197 PredecessorHalfFin13Atom1199 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1271 PredecessorHalfFin13Atom1273 PredecessorHalfFin13Atom1275
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1357
    PredecessorHalfFin13Atom1359 PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1489
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1899
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom2029 PredecessorHalfFin13Atom2155 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27183 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom1194 chi ∧
      ¬PredecessorHalfFin13Atom1196 chi ∧
      ¬PredecessorHalfFin13Atom1197 chi ∧
      ¬PredecessorHalfFin13Atom1199 chi ∧
      ¬PredecessorHalfFin13Atom1201 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 3, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5901
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1193 PredecessorHalfFin13Atom1194 PredecessorHalfFin13Atom1196
    PredecessorHalfFin13Atom1197 PredecessorHalfFin13Atom1199 PredecessorHalfFin13Atom1201
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1281
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1363
    PredecessorHalfFin13Atom1365 PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1905
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom2033 PredecessorHalfFin13Atom2159 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27187 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 6, 7, 8}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0501
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1205
    PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1216
    PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1237
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1372
    PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1427
    PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1917
    PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom2163 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27188 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 6, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0757
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1206
    PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1217
    PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1238
    PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1373
    PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1428
    PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1918
    PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom2164 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27189 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 6, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1269
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1207
    PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1213 PredecessorHalfFin13Atom1218
    PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1239
    PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1374
    PredecessorHalfFin13Atom1379 PredecessorHalfFin13Atom1394 PredecessorHalfFin13Atom1429
    PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1919
    PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom2165 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27191 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 6, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4341
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1209
    PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1215 PredecessorHalfFin13Atom1220
    PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1236 PredecessorHalfFin13Atom1241
    PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1381 PredecessorHalfFin13Atom1396 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1916 PredecessorHalfFin13Atom1921
    PredecessorHalfFin13Atom1936 PredecessorHalfFin13Atom1971 PredecessorHalfFin13Atom2167 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27192 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 6, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0885
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1206
    PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1221
    PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1242
    PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1373
    PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1432
    PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1922
    PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom2168 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27193 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 6, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1397
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1207
    PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1213 PredecessorHalfFin13Atom1222
    PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1243
    PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1374
    PredecessorHalfFin13Atom1383 PredecessorHalfFin13Atom1398 PredecessorHalfFin13Atom1433
    PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1923
    PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom2169 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27195 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 6, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4469
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1209
    PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1215 PredecessorHalfFin13Atom1224
    PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1236 PredecessorHalfFin13Atom1245
    PredecessorHalfFin13Atom1260 PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1385 PredecessorHalfFin13Atom1400 PredecessorHalfFin13Atom1435
    PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1916 PredecessorHalfFin13Atom1925
    PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom1975 PredecessorHalfFin13Atom2171 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27196 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 6, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1653
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1207
    PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1213 PredecessorHalfFin13Atom1225
    PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1246
    PredecessorHalfFin13Atom1261 PredecessorHalfFin13Atom1373 PredecessorHalfFin13Atom1374
    PredecessorHalfFin13Atom1386 PredecessorHalfFin13Atom1401 PredecessorHalfFin13Atom1436
    PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1926
    PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom2172 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27198 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 6, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4725
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1209
    PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1215 PredecessorHalfFin13Atom1227
    PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1236 PredecessorHalfFin13Atom1248
    PredecessorHalfFin13Atom1263 PredecessorHalfFin13Atom1373 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1388 PredecessorHalfFin13Atom1403 PredecessorHalfFin13Atom1438
    PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1916 PredecessorHalfFin13Atom1928
    PredecessorHalfFin13Atom1943 PredecessorHalfFin13Atom1978 PredecessorHalfFin13Atom2174 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27200 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1203 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 6, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5237
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1203 PredecessorHalfFin13Atom1207 PredecessorHalfFin13Atom1209
    PredecessorHalfFin13Atom1213 PredecessorHalfFin13Atom1215 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1236 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1265 PredecessorHalfFin13Atom1374 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1390 PredecessorHalfFin13Atom1405 PredecessorHalfFin13Atom1440
    PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1916 PredecessorHalfFin13Atom1930
    PredecessorHalfFin13Atom1945 PredecessorHalfFin13Atom1980 PredecessorHalfFin13Atom2176 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27202 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0949
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1206
    PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1221
    PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1242
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1378
    PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1442
    PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1922
    PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom2178 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27203 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1461
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1207
    PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1218 PredecessorHalfFin13Atom1222
    PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1243
    PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1379
    PredecessorHalfFin13Atom1383 PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1443
    PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1923
    PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom2179 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27205 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4533
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1209
    PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1220 PredecessorHalfFin13Atom1224
    PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1241 PredecessorHalfFin13Atom1245
    PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1381
    PredecessorHalfFin13Atom1385 PredecessorHalfFin13Atom1410 PredecessorHalfFin13Atom1445
    PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1921 PredecessorHalfFin13Atom1925
    PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom1985 PredecessorHalfFin13Atom2181 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27206 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1717
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1207
    PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1218 PredecessorHalfFin13Atom1225
    PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1246
    PredecessorHalfFin13Atom1271 PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1379
    PredecessorHalfFin13Atom1386 PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1446
    PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1926
    PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom2182 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27208 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4789
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1209
    PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1220 PredecessorHalfFin13Atom1227
    PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1241 PredecessorHalfFin13Atom1248
    PredecessorHalfFin13Atom1273 PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1381
    PredecessorHalfFin13Atom1388 PredecessorHalfFin13Atom1413 PredecessorHalfFin13Atom1448
    PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1921 PredecessorHalfFin13Atom1928
    PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom1988 PredecessorHalfFin13Atom2184 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27210 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1204 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5301
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1204 PredecessorHalfFin13Atom1207 PredecessorHalfFin13Atom1209
    PredecessorHalfFin13Atom1218 PredecessorHalfFin13Atom1220 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1241 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1275 PredecessorHalfFin13Atom1379 PredecessorHalfFin13Atom1381
    PredecessorHalfFin13Atom1390 PredecessorHalfFin13Atom1415 PredecessorHalfFin13Atom1450
    PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1921 PredecessorHalfFin13Atom1930
    PredecessorHalfFin13Atom1955 PredecessorHalfFin13Atom1990 PredecessorHalfFin13Atom2186 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27212 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1845
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1207
    PredecessorHalfFin13Atom1221 PredecessorHalfFin13Atom1222 PredecessorHalfFin13Atom1225
    PredecessorHalfFin13Atom1242 PredecessorHalfFin13Atom1243 PredecessorHalfFin13Atom1246
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1383
    PredecessorHalfFin13Atom1386 PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1452
    PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1926
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom2188 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27214 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4917
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1209
    PredecessorHalfFin13Atom1221 PredecessorHalfFin13Atom1224 PredecessorHalfFin13Atom1227
    PredecessorHalfFin13Atom1242 PredecessorHalfFin13Atom1245 PredecessorHalfFin13Atom1248
    PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1385
    PredecessorHalfFin13Atom1388 PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1454
    PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1925 PredecessorHalfFin13Atom1928
    PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom2190 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27216 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1205 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5429
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1205 PredecessorHalfFin13Atom1207 PredecessorHalfFin13Atom1209
    PredecessorHalfFin13Atom1222 PredecessorHalfFin13Atom1224 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1243 PredecessorHalfFin13Atom1245 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1281 PredecessorHalfFin13Atom1383 PredecessorHalfFin13Atom1385
    PredecessorHalfFin13Atom1390 PredecessorHalfFin13Atom1421 PredecessorHalfFin13Atom1456
    PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1925 PredecessorHalfFin13Atom1930
    PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom2192 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27219 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1206 chi ∧
      ¬PredecessorHalfFin13Atom1207 chi ∧
      ¬PredecessorHalfFin13Atom1209 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 5, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5685
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1206 PredecessorHalfFin13Atom1207 PredecessorHalfFin13Atom1209
    PredecessorHalfFin13Atom1225 PredecessorHalfFin13Atom1227 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1246 PredecessorHalfFin13Atom1248 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1386 PredecessorHalfFin13Atom1388
    PredecessorHalfFin13Atom1390 PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1459
    PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1928 PredecessorHalfFin13Atom1930
    PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2195 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27222 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0981
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1212
    PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1221
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1257
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1393
    PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1462
    PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1937
    PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2198 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27223 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 6, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1493
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1213
    PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1218 PredecessorHalfFin13Atom1222
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1258
    PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1394
    PredecessorHalfFin13Atom1398 PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1463
    PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1938
    PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2199 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27225 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 6, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4565
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1215
    PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1220 PredecessorHalfFin13Atom1224
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1260
    PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1396
    PredecessorHalfFin13Atom1400 PredecessorHalfFin13Atom1410 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1936 PredecessorHalfFin13Atom1940
    PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom2005 PredecessorHalfFin13Atom2201 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27226 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1749
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1213
    PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1218 PredecessorHalfFin13Atom1225
    PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1261
    PredecessorHalfFin13Atom1271 PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1394
    PredecessorHalfFin13Atom1401 PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1466
    PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1941
    PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2202 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27228 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4821
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1215
    PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1220 PredecessorHalfFin13Atom1227
    PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1263
    PredecessorHalfFin13Atom1273 PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1396
    PredecessorHalfFin13Atom1403 PredecessorHalfFin13Atom1413 PredecessorHalfFin13Atom1468
    PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1936 PredecessorHalfFin13Atom1943
    PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom2008 PredecessorHalfFin13Atom2204 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27230 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1210 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5333
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1210 PredecessorHalfFin13Atom1213 PredecessorHalfFin13Atom1215
    PredecessorHalfFin13Atom1218 PredecessorHalfFin13Atom1220 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1275 PredecessorHalfFin13Atom1394 PredecessorHalfFin13Atom1396
    PredecessorHalfFin13Atom1405 PredecessorHalfFin13Atom1415 PredecessorHalfFin13Atom1470
    PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1936 PredecessorHalfFin13Atom1945
    PredecessorHalfFin13Atom1955 PredecessorHalfFin13Atom2010 PredecessorHalfFin13Atom2206 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27232 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 6, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1877
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1213
    PredecessorHalfFin13Atom1221 PredecessorHalfFin13Atom1222 PredecessorHalfFin13Atom1225
    PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1261
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1398
    PredecessorHalfFin13Atom1401 PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1472
    PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1941
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2208 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27234 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 6, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4949
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1215
    PredecessorHalfFin13Atom1221 PredecessorHalfFin13Atom1224 PredecessorHalfFin13Atom1227
    PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1260 PredecessorHalfFin13Atom1263
    PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1400
    PredecessorHalfFin13Atom1403 PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1474
    PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom1943
    PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom2014 PredecessorHalfFin13Atom2210 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27236 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1211 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5461
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1211 PredecessorHalfFin13Atom1213 PredecessorHalfFin13Atom1215
    PredecessorHalfFin13Atom1222 PredecessorHalfFin13Atom1224 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1260 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1281 PredecessorHalfFin13Atom1398 PredecessorHalfFin13Atom1400
    PredecessorHalfFin13Atom1405 PredecessorHalfFin13Atom1421 PredecessorHalfFin13Atom1476
    PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom1945
    PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom2016 PredecessorHalfFin13Atom2212 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27239 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1212 chi ∧
      ¬PredecessorHalfFin13Atom1213 chi ∧
      ¬PredecessorHalfFin13Atom1215 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5717
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1212 PredecessorHalfFin13Atom1213 PredecessorHalfFin13Atom1215
    PredecessorHalfFin13Atom1225 PredecessorHalfFin13Atom1227 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1261 PredecessorHalfFin13Atom1263 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1401 PredecessorHalfFin13Atom1403
    PredecessorHalfFin13Atom1405 PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1479
    PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1943 PredecessorHalfFin13Atom1945
    PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2215 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27242 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1941
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1218
    PredecessorHalfFin13Atom1221 PredecessorHalfFin13Atom1222 PredecessorHalfFin13Atom1225
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1271
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1408
    PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1482
    PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1951
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2218 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27244 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5013
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1220
    PredecessorHalfFin13Atom1221 PredecessorHalfFin13Atom1224 PredecessorHalfFin13Atom1227
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1273
    PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1410
    PredecessorHalfFin13Atom1413 PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom1953
    PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom2024 PredecessorHalfFin13Atom2220 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27246 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1216 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5525
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1216 PredecessorHalfFin13Atom1218 PredecessorHalfFin13Atom1220
    PredecessorHalfFin13Atom1222 PredecessorHalfFin13Atom1224 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1275
    PredecessorHalfFin13Atom1281 PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1410
    PredecessorHalfFin13Atom1415 PredecessorHalfFin13Atom1421 PredecessorHalfFin13Atom1486
    PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom1955
    PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom2026 PredecessorHalfFin13Atom2222 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27249 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1217 chi ∧
      ¬PredecessorHalfFin13Atom1218 chi ∧
      ¬PredecessorHalfFin13Atom1220 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5781
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1217 PredecessorHalfFin13Atom1218 PredecessorHalfFin13Atom1220
    PredecessorHalfFin13Atom1225 PredecessorHalfFin13Atom1227 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1271 PredecessorHalfFin13Atom1273 PredecessorHalfFin13Atom1275
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1413
    PredecessorHalfFin13Atom1415 PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1489
    PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom1955
    PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom2029 PredecessorHalfFin13Atom2225 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27253 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1221 chi ∧
      ¬PredecessorHalfFin13Atom1222 chi ∧
      ¬PredecessorHalfFin13Atom1224 chi ∧
      ¬PredecessorHalfFin13Atom1225 chi ∧
      ¬PredecessorHalfFin13Atom1227 chi ∧
      ¬PredecessorHalfFin13Atom1229 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 4, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5909
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1221 PredecessorHalfFin13Atom1222 PredecessorHalfFin13Atom1224
    PredecessorHalfFin13Atom1225 PredecessorHalfFin13Atom1227 PredecessorHalfFin13Atom1229
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1281
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1419
    PredecessorHalfFin13Atom1421 PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom1961
    PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom2033 PredecessorHalfFin13Atom2229 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27257 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0997
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1233
    PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1242
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1257
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1428
    PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1462
    PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1972
    PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2233 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27258 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 6, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1509
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1234
    PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1243
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1258
    PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1429
    PredecessorHalfFin13Atom1433 PredecessorHalfFin13Atom1443 PredecessorHalfFin13Atom1463
    PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1973
    PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2234 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27260 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 6, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4581
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1236
    PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1241 PredecessorHalfFin13Atom1245
    PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1260
    PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1435 PredecessorHalfFin13Atom1445 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1971 PredecessorHalfFin13Atom1975
    PredecessorHalfFin13Atom1985 PredecessorHalfFin13Atom2005 PredecessorHalfFin13Atom2236 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27261 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1765
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1234
    PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1246
    PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1261
    PredecessorHalfFin13Atom1271 PredecessorHalfFin13Atom1428 PredecessorHalfFin13Atom1429
    PredecessorHalfFin13Atom1436 PredecessorHalfFin13Atom1446 PredecessorHalfFin13Atom1466
    PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1976
    PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2237 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27263 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4837
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1236
    PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1241 PredecessorHalfFin13Atom1248
    PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1263
    PredecessorHalfFin13Atom1273 PredecessorHalfFin13Atom1428 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1438 PredecessorHalfFin13Atom1448 PredecessorHalfFin13Atom1468
    PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1971 PredecessorHalfFin13Atom1978
    PredecessorHalfFin13Atom1988 PredecessorHalfFin13Atom2008 PredecessorHalfFin13Atom2239 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27265 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1231 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5349
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1231 PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1236
    PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1241 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1256 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1275 PredecessorHalfFin13Atom1429 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1440 PredecessorHalfFin13Atom1450 PredecessorHalfFin13Atom1470
    PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1971 PredecessorHalfFin13Atom1980
    PredecessorHalfFin13Atom1990 PredecessorHalfFin13Atom2010 PredecessorHalfFin13Atom2241 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27267 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 6, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1893
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1234
    PredecessorHalfFin13Atom1242 PredecessorHalfFin13Atom1243 PredecessorHalfFin13Atom1246
    PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1261
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1433
    PredecessorHalfFin13Atom1436 PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1472
    PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1976
    PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2243 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27269 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 6, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4965
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1236
    PredecessorHalfFin13Atom1242 PredecessorHalfFin13Atom1245 PredecessorHalfFin13Atom1248
    PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1260 PredecessorHalfFin13Atom1263
    PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1435
    PredecessorHalfFin13Atom1438 PredecessorHalfFin13Atom1454 PredecessorHalfFin13Atom1474
    PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1975 PredecessorHalfFin13Atom1978
    PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom2014 PredecessorHalfFin13Atom2245 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27271 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1232 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5477
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1232 PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1236
    PredecessorHalfFin13Atom1243 PredecessorHalfFin13Atom1245 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1260 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1281 PredecessorHalfFin13Atom1433 PredecessorHalfFin13Atom1435
    PredecessorHalfFin13Atom1440 PredecessorHalfFin13Atom1456 PredecessorHalfFin13Atom1476
    PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1975 PredecessorHalfFin13Atom1980
    PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom2016 PredecessorHalfFin13Atom2247 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27274 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1233 chi ∧
      ¬PredecessorHalfFin13Atom1234 chi ∧
      ¬PredecessorHalfFin13Atom1236 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5733
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1233 PredecessorHalfFin13Atom1234 PredecessorHalfFin13Atom1236
    PredecessorHalfFin13Atom1246 PredecessorHalfFin13Atom1248 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1261 PredecessorHalfFin13Atom1263 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1436 PredecessorHalfFin13Atom1438
    PredecessorHalfFin13Atom1440 PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1479
    PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1978 PredecessorHalfFin13Atom1980
    PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2250 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27277 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1957
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1239
    PredecessorHalfFin13Atom1242 PredecessorHalfFin13Atom1243 PredecessorHalfFin13Atom1246
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1271
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1443
    PredecessorHalfFin13Atom1446 PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1482
    PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom1986
    PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2253 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27279 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5029
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1241
    PredecessorHalfFin13Atom1242 PredecessorHalfFin13Atom1245 PredecessorHalfFin13Atom1248
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1273
    PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1445
    PredecessorHalfFin13Atom1448 PredecessorHalfFin13Atom1454 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1985 PredecessorHalfFin13Atom1988
    PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom2024 PredecessorHalfFin13Atom2255 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27281 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1237 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5541
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1237 PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1241
    PredecessorHalfFin13Atom1243 PredecessorHalfFin13Atom1245 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1275
    PredecessorHalfFin13Atom1281 PredecessorHalfFin13Atom1443 PredecessorHalfFin13Atom1445
    PredecessorHalfFin13Atom1450 PredecessorHalfFin13Atom1456 PredecessorHalfFin13Atom1486
    PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom1985 PredecessorHalfFin13Atom1990
    PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom2026 PredecessorHalfFin13Atom2257 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27284 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1238 chi ∧
      ¬PredecessorHalfFin13Atom1239 chi ∧
      ¬PredecessorHalfFin13Atom1241 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5797
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1238 PredecessorHalfFin13Atom1239 PredecessorHalfFin13Atom1241
    PredecessorHalfFin13Atom1246 PredecessorHalfFin13Atom1248 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1271 PredecessorHalfFin13Atom1273 PredecessorHalfFin13Atom1275
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1446 PredecessorHalfFin13Atom1448
    PredecessorHalfFin13Atom1450 PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1489
    PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1988 PredecessorHalfFin13Atom1990
    PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2029 PredecessorHalfFin13Atom2260 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27288 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1242 chi ∧
      ¬PredecessorHalfFin13Atom1243 chi ∧
      ¬PredecessorHalfFin13Atom1245 chi ∧
      ¬PredecessorHalfFin13Atom1246 chi ∧
      ¬PredecessorHalfFin13Atom1248 chi ∧
      ¬PredecessorHalfFin13Atom1250 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 5, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5925
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1242 PredecessorHalfFin13Atom1243 PredecessorHalfFin13Atom1245
    PredecessorHalfFin13Atom1246 PredecessorHalfFin13Atom1248 PredecessorHalfFin13Atom1250
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1281
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1454
    PredecessorHalfFin13Atom1456 PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom1996
    PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2033 PredecessorHalfFin13Atom2264 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27292 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1989
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1254
    PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1261
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1271
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1462 PredecessorHalfFin13Atom1463
    PredecessorHalfFin13Atom1466 PredecessorHalfFin13Atom1472 PredecessorHalfFin13Atom1482
    PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2006
    PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2268 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27294 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5061
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1256
    PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1260 PredecessorHalfFin13Atom1263
    PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1273
    PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1462 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1468 PredecessorHalfFin13Atom1474 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2005 PredecessorHalfFin13Atom2008
    PredecessorHalfFin13Atom2014 PredecessorHalfFin13Atom2024 PredecessorHalfFin13Atom2270 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27296 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1252 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5573
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1252 PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1256
    PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1260 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1270 PredecessorHalfFin13Atom1275
    PredecessorHalfFin13Atom1281 PredecessorHalfFin13Atom1463 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1470 PredecessorHalfFin13Atom1476 PredecessorHalfFin13Atom1486
    PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2005 PredecessorHalfFin13Atom2010
    PredecessorHalfFin13Atom2016 PredecessorHalfFin13Atom2026 PredecessorHalfFin13Atom2272 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27299 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1253 chi ∧
      ¬PredecessorHalfFin13Atom1254 chi ∧
      ¬PredecessorHalfFin13Atom1256 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5829
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1253 PredecessorHalfFin13Atom1254 PredecessorHalfFin13Atom1256
    PredecessorHalfFin13Atom1261 PredecessorHalfFin13Atom1263 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1271 PredecessorHalfFin13Atom1273 PredecessorHalfFin13Atom1275
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1466 PredecessorHalfFin13Atom1468
    PredecessorHalfFin13Atom1470 PredecessorHalfFin13Atom1479 PredecessorHalfFin13Atom1489
    PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2008 PredecessorHalfFin13Atom2010
    PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2029 PredecessorHalfFin13Atom2275 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27303 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1257 chi ∧
      ¬PredecessorHalfFin13Atom1258 chi ∧
      ¬PredecessorHalfFin13Atom1260 chi ∧
      ¬PredecessorHalfFin13Atom1261 chi ∧
      ¬PredecessorHalfFin13Atom1263 chi ∧
      ¬PredecessorHalfFin13Atom1265 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5957
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1257 PredecessorHalfFin13Atom1258 PredecessorHalfFin13Atom1260
    PredecessorHalfFin13Atom1261 PredecessorHalfFin13Atom1263 PredecessorHalfFin13Atom1265
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1281
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1472 PredecessorHalfFin13Atom1474
    PredecessorHalfFin13Atom1476 PredecessorHalfFin13Atom1479 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2014 PredecessorHalfFin13Atom2016
    PredecessorHalfFin13Atom2019 PredecessorHalfFin13Atom2033 PredecessorHalfFin13Atom2279 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27308 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1267 chi ∧
      ¬PredecessorHalfFin13Atom1268 chi ∧
      ¬PredecessorHalfFin13Atom1270 chi ∧
      ¬PredecessorHalfFin13Atom1271 chi ∧
      ¬PredecessorHalfFin13Atom1273 chi ∧
      ¬PredecessorHalfFin13Atom1275 chi ∧
      ¬PredecessorHalfFin13Atom1277 chi ∧
      ¬PredecessorHalfFin13Atom1279 chi ∧
      ¬PredecessorHalfFin13Atom1281 chi ∧
      ¬PredecessorHalfFin13Atom1284 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 2, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6021
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1267 PredecessorHalfFin13Atom1268 PredecessorHalfFin13Atom1270
    PredecessorHalfFin13Atom1271 PredecessorHalfFin13Atom1273 PredecessorHalfFin13Atom1275
    PredecessorHalfFin13Atom1277 PredecessorHalfFin13Atom1279 PredecessorHalfFin13Atom1281
    PredecessorHalfFin13Atom1284 PredecessorHalfFin13Atom1482 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom1486 PredecessorHalfFin13Atom1489 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2022 PredecessorHalfFin13Atom2024 PredecessorHalfFin13Atom2026
    PredecessorHalfFin13Atom2029 PredecessorHalfFin13Atom2033 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27313 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 6, 7, 8}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0505
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1289
    PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1300
    PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1321
    PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1372
    PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1427
    PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2043
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2163 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27314 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 6, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0761
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1290
    PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1301
    PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1322
    PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1373
    PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1428
    PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2044
    PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2164 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27315 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 6, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1273
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1291
    PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1297 PredecessorHalfFin13Atom1302
    PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1318 PredecessorHalfFin13Atom1323
    PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1374
    PredecessorHalfFin13Atom1379 PredecessorHalfFin13Atom1394 PredecessorHalfFin13Atom1429
    PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2045
    PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2165 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27317 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 6, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4345
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1299 PredecessorHalfFin13Atom1304
    PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1320 PredecessorHalfFin13Atom1325
    PredecessorHalfFin13Atom1340 PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1381 PredecessorHalfFin13Atom1396 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2042 PredecessorHalfFin13Atom2047
    PredecessorHalfFin13Atom2062 PredecessorHalfFin13Atom2097 PredecessorHalfFin13Atom2167 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27318 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 6, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0889
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1290
    PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1305
    PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1326
    PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1373
    PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1432
    PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2048
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2168 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27319 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 6, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1401
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1291
    PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1297 PredecessorHalfFin13Atom1306
    PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1318 PredecessorHalfFin13Atom1327
    PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1374
    PredecessorHalfFin13Atom1383 PredecessorHalfFin13Atom1398 PredecessorHalfFin13Atom1433
    PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2049
    PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2169 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27321 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 6, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4473
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1299 PredecessorHalfFin13Atom1308
    PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1320 PredecessorHalfFin13Atom1329
    PredecessorHalfFin13Atom1344 PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1385 PredecessorHalfFin13Atom1400 PredecessorHalfFin13Atom1435
    PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2042 PredecessorHalfFin13Atom2051
    PredecessorHalfFin13Atom2066 PredecessorHalfFin13Atom2101 PredecessorHalfFin13Atom2171 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27322 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 6, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1657
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1290 PredecessorHalfFin13Atom1291
    PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1297 PredecessorHalfFin13Atom1309
    PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1318 PredecessorHalfFin13Atom1330
    PredecessorHalfFin13Atom1345 PredecessorHalfFin13Atom1373 PredecessorHalfFin13Atom1374
    PredecessorHalfFin13Atom1386 PredecessorHalfFin13Atom1401 PredecessorHalfFin13Atom1436
    PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2052
    PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2172 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27324 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 6, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4729
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1290 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1299 PredecessorHalfFin13Atom1311
    PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1320 PredecessorHalfFin13Atom1332
    PredecessorHalfFin13Atom1347 PredecessorHalfFin13Atom1373 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1388 PredecessorHalfFin13Atom1403 PredecessorHalfFin13Atom1438
    PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2042 PredecessorHalfFin13Atom2054
    PredecessorHalfFin13Atom2069 PredecessorHalfFin13Atom2104 PredecessorHalfFin13Atom2174 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27326 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1287 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 6, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5241
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1287 PredecessorHalfFin13Atom1291 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1297 PredecessorHalfFin13Atom1299 PredecessorHalfFin13Atom1313
    PredecessorHalfFin13Atom1318 PredecessorHalfFin13Atom1320 PredecessorHalfFin13Atom1334
    PredecessorHalfFin13Atom1349 PredecessorHalfFin13Atom1374 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1390 PredecessorHalfFin13Atom1405 PredecessorHalfFin13Atom1440
    PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2042 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2071 PredecessorHalfFin13Atom2106 PredecessorHalfFin13Atom2176 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27328 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0953
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1290
    PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1305
    PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1326
    PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1378
    PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1442
    PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2048
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2178 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27329 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1465
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1291
    PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1302 PredecessorHalfFin13Atom1306
    PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1323 PredecessorHalfFin13Atom1327
    PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1379
    PredecessorHalfFin13Atom1383 PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1443
    PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2049
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2179 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27331 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4537
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1304 PredecessorHalfFin13Atom1308
    PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1325 PredecessorHalfFin13Atom1329
    PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1381
    PredecessorHalfFin13Atom1385 PredecessorHalfFin13Atom1410 PredecessorHalfFin13Atom1445
    PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2047 PredecessorHalfFin13Atom2051
    PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2111 PredecessorHalfFin13Atom2181 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27332 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1721
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1290 PredecessorHalfFin13Atom1291
    PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1302 PredecessorHalfFin13Atom1309
    PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1323 PredecessorHalfFin13Atom1330
    PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1379
    PredecessorHalfFin13Atom1386 PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1446
    PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2052
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2182 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27334 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4793
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1290 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1304 PredecessorHalfFin13Atom1311
    PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1325 PredecessorHalfFin13Atom1332
    PredecessorHalfFin13Atom1357 PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1381
    PredecessorHalfFin13Atom1388 PredecessorHalfFin13Atom1413 PredecessorHalfFin13Atom1448
    PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2047 PredecessorHalfFin13Atom2054
    PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2184 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27336 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1288 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5305
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1288 PredecessorHalfFin13Atom1291 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1302 PredecessorHalfFin13Atom1304 PredecessorHalfFin13Atom1313
    PredecessorHalfFin13Atom1323 PredecessorHalfFin13Atom1325 PredecessorHalfFin13Atom1334
    PredecessorHalfFin13Atom1359 PredecessorHalfFin13Atom1379 PredecessorHalfFin13Atom1381
    PredecessorHalfFin13Atom1390 PredecessorHalfFin13Atom1415 PredecessorHalfFin13Atom1450
    PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2047 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2081 PredecessorHalfFin13Atom2116 PredecessorHalfFin13Atom2186 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27338 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1849
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1290 PredecessorHalfFin13Atom1291
    PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1306 PredecessorHalfFin13Atom1309
    PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1327 PredecessorHalfFin13Atom1330
    PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1383
    PredecessorHalfFin13Atom1386 PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1452
    PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2052
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2188 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27340 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4921
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1290 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1308 PredecessorHalfFin13Atom1311
    PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1329 PredecessorHalfFin13Atom1332
    PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1385
    PredecessorHalfFin13Atom1388 PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1454
    PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2051 PredecessorHalfFin13Atom2054
    PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2190 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27342 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1289 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5433
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1289 PredecessorHalfFin13Atom1291 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1306 PredecessorHalfFin13Atom1308 PredecessorHalfFin13Atom1313
    PredecessorHalfFin13Atom1327 PredecessorHalfFin13Atom1329 PredecessorHalfFin13Atom1334
    PredecessorHalfFin13Atom1365 PredecessorHalfFin13Atom1383 PredecessorHalfFin13Atom1385
    PredecessorHalfFin13Atom1390 PredecessorHalfFin13Atom1421 PredecessorHalfFin13Atom1456
    PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2051 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2192 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27345 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1290 chi ∧
      ¬PredecessorHalfFin13Atom1291 chi ∧
      ¬PredecessorHalfFin13Atom1293 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 5, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5689
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1290 PredecessorHalfFin13Atom1291 PredecessorHalfFin13Atom1293
    PredecessorHalfFin13Atom1309 PredecessorHalfFin13Atom1311 PredecessorHalfFin13Atom1313
    PredecessorHalfFin13Atom1330 PredecessorHalfFin13Atom1332 PredecessorHalfFin13Atom1334
    PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1386 PredecessorHalfFin13Atom1388
    PredecessorHalfFin13Atom1390 PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1459
    PredecessorHalfFin13Atom2052 PredecessorHalfFin13Atom2054 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2195 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27348 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0985
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1296
    PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1305
    PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1341
    PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1393
    PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1462
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2063
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2198 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27349 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 6, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1497
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1297
    PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1302 PredecessorHalfFin13Atom1306
    PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1342
    PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1394
    PredecessorHalfFin13Atom1398 PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1463
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2064
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2199 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27351 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 6, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4569
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1299
    PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1304 PredecessorHalfFin13Atom1308
    PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1340 PredecessorHalfFin13Atom1344
    PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1396
    PredecessorHalfFin13Atom1400 PredecessorHalfFin13Atom1410 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2062 PredecessorHalfFin13Atom2066
    PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2131 PredecessorHalfFin13Atom2201 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27352 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1753
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1297
    PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1302 PredecessorHalfFin13Atom1309
    PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1345
    PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1394
    PredecessorHalfFin13Atom1401 PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1466
    PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2067
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2202 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27354 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4825
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1299
    PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1304 PredecessorHalfFin13Atom1311
    PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1340 PredecessorHalfFin13Atom1347
    PredecessorHalfFin13Atom1357 PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1396
    PredecessorHalfFin13Atom1403 PredecessorHalfFin13Atom1413 PredecessorHalfFin13Atom1468
    PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2062 PredecessorHalfFin13Atom2069
    PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2134 PredecessorHalfFin13Atom2204 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27356 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1294 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5337
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1294 PredecessorHalfFin13Atom1297 PredecessorHalfFin13Atom1299
    PredecessorHalfFin13Atom1302 PredecessorHalfFin13Atom1304 PredecessorHalfFin13Atom1313
    PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1340 PredecessorHalfFin13Atom1349
    PredecessorHalfFin13Atom1359 PredecessorHalfFin13Atom1394 PredecessorHalfFin13Atom1396
    PredecessorHalfFin13Atom1405 PredecessorHalfFin13Atom1415 PredecessorHalfFin13Atom1470
    PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2062 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2081 PredecessorHalfFin13Atom2136 PredecessorHalfFin13Atom2206 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27358 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 6, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1881
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1297
    PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1306 PredecessorHalfFin13Atom1309
    PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1345
    PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1398
    PredecessorHalfFin13Atom1401 PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1472
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2067
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2208 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27360 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 6, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4953
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1299
    PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1308 PredecessorHalfFin13Atom1311
    PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1344 PredecessorHalfFin13Atom1347
    PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1400
    PredecessorHalfFin13Atom1403 PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1474
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2066 PredecessorHalfFin13Atom2069
    PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2140 PredecessorHalfFin13Atom2210 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27362 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1295 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5465
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1295 PredecessorHalfFin13Atom1297 PredecessorHalfFin13Atom1299
    PredecessorHalfFin13Atom1306 PredecessorHalfFin13Atom1308 PredecessorHalfFin13Atom1313
    PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1344 PredecessorHalfFin13Atom1349
    PredecessorHalfFin13Atom1365 PredecessorHalfFin13Atom1398 PredecessorHalfFin13Atom1400
    PredecessorHalfFin13Atom1405 PredecessorHalfFin13Atom1421 PredecessorHalfFin13Atom1476
    PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2066 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2212 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27365 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1296 chi ∧
      ¬PredecessorHalfFin13Atom1297 chi ∧
      ¬PredecessorHalfFin13Atom1299 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5721
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1296 PredecessorHalfFin13Atom1297 PredecessorHalfFin13Atom1299
    PredecessorHalfFin13Atom1309 PredecessorHalfFin13Atom1311 PredecessorHalfFin13Atom1313
    PredecessorHalfFin13Atom1345 PredecessorHalfFin13Atom1347 PredecessorHalfFin13Atom1349
    PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1401 PredecessorHalfFin13Atom1403
    PredecessorHalfFin13Atom1405 PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1479
    PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2069 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2215 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27368 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1945
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1302
    PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1306 PredecessorHalfFin13Atom1309
    PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1355
    PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1408
    PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1482
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2077
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2218 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27370 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5017
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1304
    PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1308 PredecessorHalfFin13Atom1311
    PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1357
    PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1410
    PredecessorHalfFin13Atom1413 PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2079
    PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2150 PredecessorHalfFin13Atom2220 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27372 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1300 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5529
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1300 PredecessorHalfFin13Atom1302 PredecessorHalfFin13Atom1304
    PredecessorHalfFin13Atom1306 PredecessorHalfFin13Atom1308 PredecessorHalfFin13Atom1313
    PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1359
    PredecessorHalfFin13Atom1365 PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1410
    PredecessorHalfFin13Atom1415 PredecessorHalfFin13Atom1421 PredecessorHalfFin13Atom1486
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2081
    PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2152 PredecessorHalfFin13Atom2222 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27375 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1301 chi ∧
      ¬PredecessorHalfFin13Atom1302 chi ∧
      ¬PredecessorHalfFin13Atom1304 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5785
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1301 PredecessorHalfFin13Atom1302 PredecessorHalfFin13Atom1304
    PredecessorHalfFin13Atom1309 PredecessorHalfFin13Atom1311 PredecessorHalfFin13Atom1313
    PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1357 PredecessorHalfFin13Atom1359
    PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1413
    PredecessorHalfFin13Atom1415 PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1489
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2081
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2225 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27379 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1305 chi ∧
      ¬PredecessorHalfFin13Atom1306 chi ∧
      ¬PredecessorHalfFin13Atom1308 chi ∧
      ¬PredecessorHalfFin13Atom1309 chi ∧
      ¬PredecessorHalfFin13Atom1311 chi ∧
      ¬PredecessorHalfFin13Atom1313 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 4, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5913
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1305 PredecessorHalfFin13Atom1306 PredecessorHalfFin13Atom1308
    PredecessorHalfFin13Atom1309 PredecessorHalfFin13Atom1311 PredecessorHalfFin13Atom1313
    PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1365
    PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1419
    PredecessorHalfFin13Atom1421 PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2087
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2159 PredecessorHalfFin13Atom2229 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27383 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1001
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1317
    PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1326
    PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1341
    PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1428
    PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1462
    PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2098
    PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2233 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27384 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 6, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1513
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1318
    PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1323 PredecessorHalfFin13Atom1327
    PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1342
    PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1429
    PredecessorHalfFin13Atom1433 PredecessorHalfFin13Atom1443 PredecessorHalfFin13Atom1463
    PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2099
    PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2234 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27386 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 6, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4585
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1320
    PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1325 PredecessorHalfFin13Atom1329
    PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1340 PredecessorHalfFin13Atom1344
    PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1435 PredecessorHalfFin13Atom1445 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2097 PredecessorHalfFin13Atom2101
    PredecessorHalfFin13Atom2111 PredecessorHalfFin13Atom2131 PredecessorHalfFin13Atom2236 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27387 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1769
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1318
    PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1323 PredecessorHalfFin13Atom1330
    PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1345
    PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1428 PredecessorHalfFin13Atom1429
    PredecessorHalfFin13Atom1436 PredecessorHalfFin13Atom1446 PredecessorHalfFin13Atom1466
    PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2102
    PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2237 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27389 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4841
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1320
    PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1325 PredecessorHalfFin13Atom1332
    PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1340 PredecessorHalfFin13Atom1347
    PredecessorHalfFin13Atom1357 PredecessorHalfFin13Atom1428 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1438 PredecessorHalfFin13Atom1448 PredecessorHalfFin13Atom1468
    PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2097 PredecessorHalfFin13Atom2104
    PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2134 PredecessorHalfFin13Atom2239 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27391 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1315 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5353
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1315 PredecessorHalfFin13Atom1318 PredecessorHalfFin13Atom1320
    PredecessorHalfFin13Atom1323 PredecessorHalfFin13Atom1325 PredecessorHalfFin13Atom1334
    PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1340 PredecessorHalfFin13Atom1349
    PredecessorHalfFin13Atom1359 PredecessorHalfFin13Atom1429 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1440 PredecessorHalfFin13Atom1450 PredecessorHalfFin13Atom1470
    PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2097 PredecessorHalfFin13Atom2106
    PredecessorHalfFin13Atom2116 PredecessorHalfFin13Atom2136 PredecessorHalfFin13Atom2241 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27393 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 6, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1897
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1318
    PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1327 PredecessorHalfFin13Atom1330
    PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1345
    PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1433
    PredecessorHalfFin13Atom1436 PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1472
    PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2102
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2243 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27395 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 6, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4969
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1320
    PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1329 PredecessorHalfFin13Atom1332
    PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1344 PredecessorHalfFin13Atom1347
    PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1435
    PredecessorHalfFin13Atom1438 PredecessorHalfFin13Atom1454 PredecessorHalfFin13Atom1474
    PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2101 PredecessorHalfFin13Atom2104
    PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2140 PredecessorHalfFin13Atom2245 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27397 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1316 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5481
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1316 PredecessorHalfFin13Atom1318 PredecessorHalfFin13Atom1320
    PredecessorHalfFin13Atom1327 PredecessorHalfFin13Atom1329 PredecessorHalfFin13Atom1334
    PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1344 PredecessorHalfFin13Atom1349
    PredecessorHalfFin13Atom1365 PredecessorHalfFin13Atom1433 PredecessorHalfFin13Atom1435
    PredecessorHalfFin13Atom1440 PredecessorHalfFin13Atom1456 PredecessorHalfFin13Atom1476
    PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2101 PredecessorHalfFin13Atom2106
    PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2247 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27400 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1317 chi ∧
      ¬PredecessorHalfFin13Atom1318 chi ∧
      ¬PredecessorHalfFin13Atom1320 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5737
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1317 PredecessorHalfFin13Atom1318 PredecessorHalfFin13Atom1320
    PredecessorHalfFin13Atom1330 PredecessorHalfFin13Atom1332 PredecessorHalfFin13Atom1334
    PredecessorHalfFin13Atom1345 PredecessorHalfFin13Atom1347 PredecessorHalfFin13Atom1349
    PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1436 PredecessorHalfFin13Atom1438
    PredecessorHalfFin13Atom1440 PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1479
    PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2104 PredecessorHalfFin13Atom2106
    PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2250 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27403 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1961
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1323
    PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1327 PredecessorHalfFin13Atom1330
    PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1355
    PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1443
    PredecessorHalfFin13Atom1446 PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1482
    PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2112
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2253 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27405 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5033
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1325
    PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1329 PredecessorHalfFin13Atom1332
    PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1357
    PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1445
    PredecessorHalfFin13Atom1448 PredecessorHalfFin13Atom1454 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2111 PredecessorHalfFin13Atom2114
    PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2150 PredecessorHalfFin13Atom2255 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27407 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1321 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5545
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1321 PredecessorHalfFin13Atom1323 PredecessorHalfFin13Atom1325
    PredecessorHalfFin13Atom1327 PredecessorHalfFin13Atom1329 PredecessorHalfFin13Atom1334
    PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1359
    PredecessorHalfFin13Atom1365 PredecessorHalfFin13Atom1443 PredecessorHalfFin13Atom1445
    PredecessorHalfFin13Atom1450 PredecessorHalfFin13Atom1456 PredecessorHalfFin13Atom1486
    PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2111 PredecessorHalfFin13Atom2116
    PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2152 PredecessorHalfFin13Atom2257 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27410 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1322 chi ∧
      ¬PredecessorHalfFin13Atom1323 chi ∧
      ¬PredecessorHalfFin13Atom1325 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5801
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1322 PredecessorHalfFin13Atom1323 PredecessorHalfFin13Atom1325
    PredecessorHalfFin13Atom1330 PredecessorHalfFin13Atom1332 PredecessorHalfFin13Atom1334
    PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1357 PredecessorHalfFin13Atom1359
    PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1446 PredecessorHalfFin13Atom1448
    PredecessorHalfFin13Atom1450 PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1489
    PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2116
    PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2260 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27414 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1326 chi ∧
      ¬PredecessorHalfFin13Atom1327 chi ∧
      ¬PredecessorHalfFin13Atom1329 chi ∧
      ¬PredecessorHalfFin13Atom1330 chi ∧
      ¬PredecessorHalfFin13Atom1332 chi ∧
      ¬PredecessorHalfFin13Atom1334 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 5, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5929
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1326 PredecessorHalfFin13Atom1327 PredecessorHalfFin13Atom1329
    PredecessorHalfFin13Atom1330 PredecessorHalfFin13Atom1332 PredecessorHalfFin13Atom1334
    PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1365
    PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1454
    PredecessorHalfFin13Atom1456 PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2122
    PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2159 PredecessorHalfFin13Atom2264 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27418 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1993
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1338
    PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1345
    PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1355
    PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1462 PredecessorHalfFin13Atom1463
    PredecessorHalfFin13Atom1466 PredecessorHalfFin13Atom1472 PredecessorHalfFin13Atom1482
    PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2132
    PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2268 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

end ErdosSzekeres

end
