module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 096. -/

theorem predecessorHalfFin13_clause27420 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5065
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1340
    PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1344 PredecessorHalfFin13Atom1347
    PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1357
    PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1462 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1468 PredecessorHalfFin13Atom1474 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2131 PredecessorHalfFin13Atom2134
    PredecessorHalfFin13Atom2140 PredecessorHalfFin13Atom2150 PredecessorHalfFin13Atom2270 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27422 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1336 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5577
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1336 PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1340
    PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1344 PredecessorHalfFin13Atom1349
    PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1354 PredecessorHalfFin13Atom1359
    PredecessorHalfFin13Atom1365 PredecessorHalfFin13Atom1463 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1470 PredecessorHalfFin13Atom1476 PredecessorHalfFin13Atom1486
    PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2131 PredecessorHalfFin13Atom2136
    PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2152 PredecessorHalfFin13Atom2272 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27425 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1337 chi ∧
      ¬PredecessorHalfFin13Atom1338 chi ∧
      ¬PredecessorHalfFin13Atom1340 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5833
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1337 PredecessorHalfFin13Atom1338 PredecessorHalfFin13Atom1340
    PredecessorHalfFin13Atom1345 PredecessorHalfFin13Atom1347 PredecessorHalfFin13Atom1349
    PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1357 PredecessorHalfFin13Atom1359
    PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1466 PredecessorHalfFin13Atom1468
    PredecessorHalfFin13Atom1470 PredecessorHalfFin13Atom1479 PredecessorHalfFin13Atom1489
    PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2134 PredecessorHalfFin13Atom2136
    PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2275 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27429 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1341 chi ∧
      ¬PredecessorHalfFin13Atom1342 chi ∧
      ¬PredecessorHalfFin13Atom1344 chi ∧
      ¬PredecessorHalfFin13Atom1345 chi ∧
      ¬PredecessorHalfFin13Atom1347 chi ∧
      ¬PredecessorHalfFin13Atom1349 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5961
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1341 PredecessorHalfFin13Atom1342 PredecessorHalfFin13Atom1344
    PredecessorHalfFin13Atom1345 PredecessorHalfFin13Atom1347 PredecessorHalfFin13Atom1349
    PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1365
    PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1472 PredecessorHalfFin13Atom1474
    PredecessorHalfFin13Atom1476 PredecessorHalfFin13Atom1479 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2140 PredecessorHalfFin13Atom2142
    PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2159 PredecessorHalfFin13Atom2279 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27434 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1351 chi ∧
      ¬PredecessorHalfFin13Atom1352 chi ∧
      ¬PredecessorHalfFin13Atom1354 chi ∧
      ¬PredecessorHalfFin13Atom1355 chi ∧
      ¬PredecessorHalfFin13Atom1357 chi ∧
      ¬PredecessorHalfFin13Atom1359 chi ∧
      ¬PredecessorHalfFin13Atom1361 chi ∧
      ¬PredecessorHalfFin13Atom1363 chi ∧
      ¬PredecessorHalfFin13Atom1365 chi ∧
      ¬PredecessorHalfFin13Atom1368 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 3, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6025
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1351 PredecessorHalfFin13Atom1352 PredecessorHalfFin13Atom1354
    PredecessorHalfFin13Atom1355 PredecessorHalfFin13Atom1357 PredecessorHalfFin13Atom1359
    PredecessorHalfFin13Atom1361 PredecessorHalfFin13Atom1363 PredecessorHalfFin13Atom1365
    PredecessorHalfFin13Atom1368 PredecessorHalfFin13Atom1482 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom1486 PredecessorHalfFin13Atom1489 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2150 PredecessorHalfFin13Atom2152
    PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2159 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27439 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1009
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1373
    PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1382
    PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1397
    PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1428
    PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1462
    PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2168
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2233 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27440 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1521
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1374
    PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1379 PredecessorHalfFin13Atom1383
    PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1394 PredecessorHalfFin13Atom1398
    PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1429
    PredecessorHalfFin13Atom1433 PredecessorHalfFin13Atom1443 PredecessorHalfFin13Atom1463
    PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2169
    PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2234 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27442 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4593
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1381 PredecessorHalfFin13Atom1385
    PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1396 PredecessorHalfFin13Atom1400
    PredecessorHalfFin13Atom1410 PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1435 PredecessorHalfFin13Atom1445 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom2163 PredecessorHalfFin13Atom2167 PredecessorHalfFin13Atom2171
    PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2201 PredecessorHalfFin13Atom2236 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27443 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1777
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1373 PredecessorHalfFin13Atom1374
    PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1379 PredecessorHalfFin13Atom1386
    PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1394 PredecessorHalfFin13Atom1401
    PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1428 PredecessorHalfFin13Atom1429
    PredecessorHalfFin13Atom1436 PredecessorHalfFin13Atom1446 PredecessorHalfFin13Atom1466
    PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2172
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2237 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27445 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4849
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1373 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1381 PredecessorHalfFin13Atom1388
    PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1396 PredecessorHalfFin13Atom1403
    PredecessorHalfFin13Atom1413 PredecessorHalfFin13Atom1428 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1438 PredecessorHalfFin13Atom1448 PredecessorHalfFin13Atom1468
    PredecessorHalfFin13Atom2164 PredecessorHalfFin13Atom2167 PredecessorHalfFin13Atom2174
    PredecessorHalfFin13Atom2184 PredecessorHalfFin13Atom2204 PredecessorHalfFin13Atom2239 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27447 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1371 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5361
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1371 PredecessorHalfFin13Atom1374 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1379 PredecessorHalfFin13Atom1381 PredecessorHalfFin13Atom1390
    PredecessorHalfFin13Atom1394 PredecessorHalfFin13Atom1396 PredecessorHalfFin13Atom1405
    PredecessorHalfFin13Atom1415 PredecessorHalfFin13Atom1429 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1440 PredecessorHalfFin13Atom1450 PredecessorHalfFin13Atom1470
    PredecessorHalfFin13Atom2165 PredecessorHalfFin13Atom2167 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2186 PredecessorHalfFin13Atom2206 PredecessorHalfFin13Atom2241 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27449 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1905
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1373 PredecessorHalfFin13Atom1374
    PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1383 PredecessorHalfFin13Atom1386
    PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1398 PredecessorHalfFin13Atom1401
    PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1433
    PredecessorHalfFin13Atom1436 PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1472
    PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2172
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2243 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27451 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4977
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1373 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1385 PredecessorHalfFin13Atom1388
    PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1400 PredecessorHalfFin13Atom1403
    PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1435
    PredecessorHalfFin13Atom1438 PredecessorHalfFin13Atom1454 PredecessorHalfFin13Atom1474
    PredecessorHalfFin13Atom2168 PredecessorHalfFin13Atom2171 PredecessorHalfFin13Atom2174
    PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2245 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27453 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1372 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5489
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1372 PredecessorHalfFin13Atom1374 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1383 PredecessorHalfFin13Atom1385 PredecessorHalfFin13Atom1390
    PredecessorHalfFin13Atom1398 PredecessorHalfFin13Atom1400 PredecessorHalfFin13Atom1405
    PredecessorHalfFin13Atom1421 PredecessorHalfFin13Atom1433 PredecessorHalfFin13Atom1435
    PredecessorHalfFin13Atom1440 PredecessorHalfFin13Atom1456 PredecessorHalfFin13Atom1476
    PredecessorHalfFin13Atom2169 PredecessorHalfFin13Atom2171 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2192 PredecessorHalfFin13Atom2212 PredecessorHalfFin13Atom2247 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27456 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1373 chi ∧
      ¬PredecessorHalfFin13Atom1374 chi ∧
      ¬PredecessorHalfFin13Atom1376 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5745
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1373 PredecessorHalfFin13Atom1374 PredecessorHalfFin13Atom1376
    PredecessorHalfFin13Atom1386 PredecessorHalfFin13Atom1388 PredecessorHalfFin13Atom1390
    PredecessorHalfFin13Atom1401 PredecessorHalfFin13Atom1403 PredecessorHalfFin13Atom1405
    PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1436 PredecessorHalfFin13Atom1438
    PredecessorHalfFin13Atom1440 PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1479
    PredecessorHalfFin13Atom2172 PredecessorHalfFin13Atom2174 PredecessorHalfFin13Atom2176
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2250 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27459 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1969
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1379
    PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1383 PredecessorHalfFin13Atom1386
    PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1411
    PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1443
    PredecessorHalfFin13Atom1446 PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1482
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2182
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2253 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27461 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5041
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1381
    PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1385 PredecessorHalfFin13Atom1388
    PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1410 PredecessorHalfFin13Atom1413
    PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1445
    PredecessorHalfFin13Atom1448 PredecessorHalfFin13Atom1454 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom2178 PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2184
    PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2220 PredecessorHalfFin13Atom2255 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27463 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1377 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5553
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1377 PredecessorHalfFin13Atom1379 PredecessorHalfFin13Atom1381
    PredecessorHalfFin13Atom1383 PredecessorHalfFin13Atom1385 PredecessorHalfFin13Atom1390
    PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1410 PredecessorHalfFin13Atom1415
    PredecessorHalfFin13Atom1421 PredecessorHalfFin13Atom1443 PredecessorHalfFin13Atom1445
    PredecessorHalfFin13Atom1450 PredecessorHalfFin13Atom1456 PredecessorHalfFin13Atom1486
    PredecessorHalfFin13Atom2179 PredecessorHalfFin13Atom2181 PredecessorHalfFin13Atom2186
    PredecessorHalfFin13Atom2192 PredecessorHalfFin13Atom2222 PredecessorHalfFin13Atom2257 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27466 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1378 chi ∧
      ¬PredecessorHalfFin13Atom1379 chi ∧
      ¬PredecessorHalfFin13Atom1381 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5809
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1378 PredecessorHalfFin13Atom1379 PredecessorHalfFin13Atom1381
    PredecessorHalfFin13Atom1386 PredecessorHalfFin13Atom1388 PredecessorHalfFin13Atom1390
    PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1413 PredecessorHalfFin13Atom1415
    PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1446 PredecessorHalfFin13Atom1448
    PredecessorHalfFin13Atom1450 PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1489
    PredecessorHalfFin13Atom2182 PredecessorHalfFin13Atom2184 PredecessorHalfFin13Atom2186
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2260 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27470 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1382 chi ∧
      ¬PredecessorHalfFin13Atom1383 chi ∧
      ¬PredecessorHalfFin13Atom1385 chi ∧
      ¬PredecessorHalfFin13Atom1386 chi ∧
      ¬PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 5, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5937
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1382 PredecessorHalfFin13Atom1383 PredecessorHalfFin13Atom1385
    PredecessorHalfFin13Atom1386 PredecessorHalfFin13Atom1388 PredecessorHalfFin13Atom1390
    PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1421
    PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1454
    PredecessorHalfFin13Atom1456 PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2188 PredecessorHalfFin13Atom2190 PredecessorHalfFin13Atom2192
    PredecessorHalfFin13Atom2195 PredecessorHalfFin13Atom2229 PredecessorHalfFin13Atom2264 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27474 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2001
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1394
    PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1398 PredecessorHalfFin13Atom1401
    PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1411
    PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1462 PredecessorHalfFin13Atom1463
    PredecessorHalfFin13Atom1466 PredecessorHalfFin13Atom1472 PredecessorHalfFin13Atom1482
    PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2202
    PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2268 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27476 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5073
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1396
    PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1400 PredecessorHalfFin13Atom1403
    PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1410 PredecessorHalfFin13Atom1413
    PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1462 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1468 PredecessorHalfFin13Atom1474 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom2198 PredecessorHalfFin13Atom2201 PredecessorHalfFin13Atom2204
    PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2220 PredecessorHalfFin13Atom2270 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27478 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5585
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1392 PredecessorHalfFin13Atom1394 PredecessorHalfFin13Atom1396
    PredecessorHalfFin13Atom1398 PredecessorHalfFin13Atom1400 PredecessorHalfFin13Atom1405
    PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1410 PredecessorHalfFin13Atom1415
    PredecessorHalfFin13Atom1421 PredecessorHalfFin13Atom1463 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1470 PredecessorHalfFin13Atom1476 PredecessorHalfFin13Atom1486
    PredecessorHalfFin13Atom2199 PredecessorHalfFin13Atom2201 PredecessorHalfFin13Atom2206
    PredecessorHalfFin13Atom2212 PredecessorHalfFin13Atom2222 PredecessorHalfFin13Atom2272 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27481 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5841
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1393 PredecessorHalfFin13Atom1394 PredecessorHalfFin13Atom1396
    PredecessorHalfFin13Atom1401 PredecessorHalfFin13Atom1403 PredecessorHalfFin13Atom1405
    PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1413 PredecessorHalfFin13Atom1415
    PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1466 PredecessorHalfFin13Atom1468
    PredecessorHalfFin13Atom1470 PredecessorHalfFin13Atom1479 PredecessorHalfFin13Atom1489
    PredecessorHalfFin13Atom2202 PredecessorHalfFin13Atom2204 PredecessorHalfFin13Atom2206
    PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2275 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27485 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5969
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1397 PredecessorHalfFin13Atom1398 PredecessorHalfFin13Atom1400
    PredecessorHalfFin13Atom1401 PredecessorHalfFin13Atom1403 PredecessorHalfFin13Atom1405
    PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1421
    PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1472 PredecessorHalfFin13Atom1474
    PredecessorHalfFin13Atom1476 PredecessorHalfFin13Atom1479 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2208 PredecessorHalfFin13Atom2210 PredecessorHalfFin13Atom2212
    PredecessorHalfFin13Atom2215 PredecessorHalfFin13Atom2229 PredecessorHalfFin13Atom2279 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27490 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 4, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6033
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1407 PredecessorHalfFin13Atom1408 PredecessorHalfFin13Atom1410
    PredecessorHalfFin13Atom1411 PredecessorHalfFin13Atom1413 PredecessorHalfFin13Atom1415
    PredecessorHalfFin13Atom1417 PredecessorHalfFin13Atom1419 PredecessorHalfFin13Atom1421
    PredecessorHalfFin13Atom1424 PredecessorHalfFin13Atom1482 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom1486 PredecessorHalfFin13Atom1489 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2218 PredecessorHalfFin13Atom2220 PredecessorHalfFin13Atom2222
    PredecessorHalfFin13Atom2225 PredecessorHalfFin13Atom2229 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27495 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2017
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1428 PredecessorHalfFin13Atom1429
    PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1433 PredecessorHalfFin13Atom1436
    PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1443 PredecessorHalfFin13Atom1446
    PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1462 PredecessorHalfFin13Atom1463
    PredecessorHalfFin13Atom1466 PredecessorHalfFin13Atom1472 PredecessorHalfFin13Atom1482
    PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2237
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2268 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27497 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5089
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1428 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1435 PredecessorHalfFin13Atom1438
    PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1445 PredecessorHalfFin13Atom1448
    PredecessorHalfFin13Atom1454 PredecessorHalfFin13Atom1462 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1468 PredecessorHalfFin13Atom1474 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom2233 PredecessorHalfFin13Atom2236 PredecessorHalfFin13Atom2239
    PredecessorHalfFin13Atom2245 PredecessorHalfFin13Atom2255 PredecessorHalfFin13Atom2270 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27499 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5601
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1427 PredecessorHalfFin13Atom1429 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1433 PredecessorHalfFin13Atom1435 PredecessorHalfFin13Atom1440
    PredecessorHalfFin13Atom1443 PredecessorHalfFin13Atom1445 PredecessorHalfFin13Atom1450
    PredecessorHalfFin13Atom1456 PredecessorHalfFin13Atom1463 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1470 PredecessorHalfFin13Atom1476 PredecessorHalfFin13Atom1486
    PredecessorHalfFin13Atom2234 PredecessorHalfFin13Atom2236 PredecessorHalfFin13Atom2241
    PredecessorHalfFin13Atom2247 PredecessorHalfFin13Atom2257 PredecessorHalfFin13Atom2272 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27502 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi ∧
      ¬PredecessorHalfFin13Atom2241 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5857
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1428 PredecessorHalfFin13Atom1429 PredecessorHalfFin13Atom1431
    PredecessorHalfFin13Atom1436 PredecessorHalfFin13Atom1438 PredecessorHalfFin13Atom1440
    PredecessorHalfFin13Atom1446 PredecessorHalfFin13Atom1448 PredecessorHalfFin13Atom1450
    PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1466 PredecessorHalfFin13Atom1468
    PredecessorHalfFin13Atom1470 PredecessorHalfFin13Atom1479 PredecessorHalfFin13Atom1489
    PredecessorHalfFin13Atom2237 PredecessorHalfFin13Atom2239 PredecessorHalfFin13Atom2241
    PredecessorHalfFin13Atom2250 PredecessorHalfFin13Atom2260 PredecessorHalfFin13Atom2275 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27506 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2243 chi ∧
      ¬PredecessorHalfFin13Atom2245 chi ∧
      ¬PredecessorHalfFin13Atom2247 chi ∧
      ¬PredecessorHalfFin13Atom2250 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 6, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5985
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1432 PredecessorHalfFin13Atom1433 PredecessorHalfFin13Atom1435
    PredecessorHalfFin13Atom1436 PredecessorHalfFin13Atom1438 PredecessorHalfFin13Atom1440
    PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1454 PredecessorHalfFin13Atom1456
    PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1472 PredecessorHalfFin13Atom1474
    PredecessorHalfFin13Atom1476 PredecessorHalfFin13Atom1479 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2243 PredecessorHalfFin13Atom2245 PredecessorHalfFin13Atom2247
    PredecessorHalfFin13Atom2250 PredecessorHalfFin13Atom2264 PredecessorHalfFin13Atom2279 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27511 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2253 chi ∧
      ¬PredecessorHalfFin13Atom2255 chi ∧
      ¬PredecessorHalfFin13Atom2257 chi ∧
      ¬PredecessorHalfFin13Atom2260 chi ∧
      ¬PredecessorHalfFin13Atom2264 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 5, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6049
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1442 PredecessorHalfFin13Atom1443 PredecessorHalfFin13Atom1445
    PredecessorHalfFin13Atom1446 PredecessorHalfFin13Atom1448 PredecessorHalfFin13Atom1450
    PredecessorHalfFin13Atom1452 PredecessorHalfFin13Atom1454 PredecessorHalfFin13Atom1456
    PredecessorHalfFin13Atom1459 PredecessorHalfFin13Atom1482 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom1486 PredecessorHalfFin13Atom1489 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2253 PredecessorHalfFin13Atom2255 PredecessorHalfFin13Atom2257
    PredecessorHalfFin13Atom2260 PredecessorHalfFin13Atom2264 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27517 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom2268 chi ∧
      ¬PredecessorHalfFin13Atom2270 chi ∧
      ¬PredecessorHalfFin13Atom2272 chi ∧
      ¬PredecessorHalfFin13Atom2275 chi ∧
      ¬PredecessorHalfFin13Atom2279 chi ∧
      ¬PredecessorHalfFin13Atom2284 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 6, 7, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6081
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1462 PredecessorHalfFin13Atom1463 PredecessorHalfFin13Atom1465
    PredecessorHalfFin13Atom1466 PredecessorHalfFin13Atom1468 PredecessorHalfFin13Atom1470
    PredecessorHalfFin13Atom1472 PredecessorHalfFin13Atom1474 PredecessorHalfFin13Atom1476
    PredecessorHalfFin13Atom1479 PredecessorHalfFin13Atom1482 PredecessorHalfFin13Atom1484
    PredecessorHalfFin13Atom1486 PredecessorHalfFin13Atom1489 PredecessorHalfFin13Atom1493
    PredecessorHalfFin13Atom2268 PredecessorHalfFin13Atom2270 PredecessorHalfFin13Atom2272
    PredecessorHalfFin13Atom2275 PredecessorHalfFin13Atom2279 PredecessorHalfFin13Atom2284 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27985 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2163 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 7, 8}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0508
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1829
    PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1840
    PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1861
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1912
    PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1967
    PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2043
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2163 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27986 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2164 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0764
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1830
    PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1841
    PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1862
    PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1913
    PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1968
    PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2044
    PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2164 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27987 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2165 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1276
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1831
    PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1842
    PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1863
    PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1914
    PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1969
    PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2045
    PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2165 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27988 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2166 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 7, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2300
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1832
    PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1838 PredecessorHalfFin13Atom1843
    PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1859 PredecessorHalfFin13Atom1864
    PredecessorHalfFin13Atom1879 PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1915
    PredecessorHalfFin13Atom1920 PredecessorHalfFin13Atom1935 PredecessorHalfFin13Atom1970
    PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2041 PredecessorHalfFin13Atom2046
    PredecessorHalfFin13Atom2061 PredecessorHalfFin13Atom2096 PredecessorHalfFin13Atom2166 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27989 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom2037 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2167 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4348
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1839 PredecessorHalfFin13Atom1844
    PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1860 PredecessorHalfFin13Atom1865
    PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1911 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1921 PredecessorHalfFin13Atom1936 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom2037 PredecessorHalfFin13Atom2042 PredecessorHalfFin13Atom2047
    PredecessorHalfFin13Atom2062 PredecessorHalfFin13Atom2097 PredecessorHalfFin13Atom2167 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27990 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2168 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0892
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1830
    PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1845
    PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1866
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1913
    PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1972
    PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2048
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2168 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27991 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2169 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1404
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1831
    PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1846
    PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1867
    PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1914
    PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1973
    PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2049
    PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2169 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27992 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2170 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 8, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2428
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1832
    PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1838 PredecessorHalfFin13Atom1847
    PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1859 PredecessorHalfFin13Atom1868
    PredecessorHalfFin13Atom1883 PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1915
    PredecessorHalfFin13Atom1924 PredecessorHalfFin13Atom1939 PredecessorHalfFin13Atom1974
    PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2041 PredecessorHalfFin13Atom2050
    PredecessorHalfFin13Atom2065 PredecessorHalfFin13Atom2100 PredecessorHalfFin13Atom2170 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27993 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom2038 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2171 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4476
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1839 PredecessorHalfFin13Atom1848
    PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1860 PredecessorHalfFin13Atom1869
    PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1912 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1925 PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom1975
    PredecessorHalfFin13Atom2038 PredecessorHalfFin13Atom2042 PredecessorHalfFin13Atom2051
    PredecessorHalfFin13Atom2066 PredecessorHalfFin13Atom2101 PredecessorHalfFin13Atom2171 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27994 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2172 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1660
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1831
    PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1849
    PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1870
    PredecessorHalfFin13Atom1885 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1914
    PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1976
    PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2052
    PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2172 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27995 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2173 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2684
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1832
    PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1838 PredecessorHalfFin13Atom1850
    PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1859 PredecessorHalfFin13Atom1871
    PredecessorHalfFin13Atom1886 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1915
    PredecessorHalfFin13Atom1927 PredecessorHalfFin13Atom1942 PredecessorHalfFin13Atom1977
    PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2041 PredecessorHalfFin13Atom2053
    PredecessorHalfFin13Atom2068 PredecessorHalfFin13Atom2103 PredecessorHalfFin13Atom2173 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27996 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom2039 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2174 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4732
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1839 PredecessorHalfFin13Atom1851
    PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1860 PredecessorHalfFin13Atom1872
    PredecessorHalfFin13Atom1887 PredecessorHalfFin13Atom1913 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1928 PredecessorHalfFin13Atom1943 PredecessorHalfFin13Atom1978
    PredecessorHalfFin13Atom2039 PredecessorHalfFin13Atom2042 PredecessorHalfFin13Atom2054
    PredecessorHalfFin13Atom2069 PredecessorHalfFin13Atom2104 PredecessorHalfFin13Atom2174 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27997 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom2175 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3196
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1832
    PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1838 PredecessorHalfFin13Atom1852
    PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1859 PredecessorHalfFin13Atom1873
    PredecessorHalfFin13Atom1888 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1915
    PredecessorHalfFin13Atom1929 PredecessorHalfFin13Atom1944 PredecessorHalfFin13Atom1979
    PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2041 PredecessorHalfFin13Atom2055
    PredecessorHalfFin13Atom2070 PredecessorHalfFin13Atom2105 PredecessorHalfFin13Atom2175 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27998 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom2040 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom2176 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5244
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1839 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1860 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1889 PredecessorHalfFin13Atom1914 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1930 PredecessorHalfFin13Atom1945 PredecessorHalfFin13Atom1980
    PredecessorHalfFin13Atom2040 PredecessorHalfFin13Atom2042 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2071 PredecessorHalfFin13Atom2106 PredecessorHalfFin13Atom2176 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause27999 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1890 chi ∧
      ¬PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom2041 chi ∧
      ¬PredecessorHalfFin13Atom2042 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom2177 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 6, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6268
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1827 PredecessorHalfFin13Atom1832 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1838 PredecessorHalfFin13Atom1839 PredecessorHalfFin13Atom1854
    PredecessorHalfFin13Atom1859 PredecessorHalfFin13Atom1860 PredecessorHalfFin13Atom1875
    PredecessorHalfFin13Atom1890 PredecessorHalfFin13Atom1915 PredecessorHalfFin13Atom1916
    PredecessorHalfFin13Atom1931 PredecessorHalfFin13Atom1946 PredecessorHalfFin13Atom1981
    PredecessorHalfFin13Atom2041 PredecessorHalfFin13Atom2042 PredecessorHalfFin13Atom2057
    PredecessorHalfFin13Atom2072 PredecessorHalfFin13Atom2107 PredecessorHalfFin13Atom2177 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28000 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2178 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0956
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1830
    PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1845
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1866
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1918
    PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1982
    PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2048
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2178 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28001 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2179 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1468
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1831
    PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1846
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1867
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1919
    PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1983
    PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2049
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2179 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28002 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2180 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 8, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2492
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1832
    PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1843 PredecessorHalfFin13Atom1847
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1864 PredecessorHalfFin13Atom1868
    PredecessorHalfFin13Atom1893 PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1920
    PredecessorHalfFin13Atom1924 PredecessorHalfFin13Atom1949 PredecessorHalfFin13Atom1984
    PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2046 PredecessorHalfFin13Atom2050
    PredecessorHalfFin13Atom2075 PredecessorHalfFin13Atom2110 PredecessorHalfFin13Atom2180 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28003 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom2043 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2181 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4540
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1844 PredecessorHalfFin13Atom1848
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1865 PredecessorHalfFin13Atom1869
    PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1917 PredecessorHalfFin13Atom1921
    PredecessorHalfFin13Atom1925 PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom1985
    PredecessorHalfFin13Atom2043 PredecessorHalfFin13Atom2047 PredecessorHalfFin13Atom2051
    PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2111 PredecessorHalfFin13Atom2181 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28004 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2182 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1724
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1831
    PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1849
    PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1870
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1919
    PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1986
    PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2052
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2182 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28005 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2183 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2748
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1832
    PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1843 PredecessorHalfFin13Atom1850
    PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1864 PredecessorHalfFin13Atom1871
    PredecessorHalfFin13Atom1896 PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1920
    PredecessorHalfFin13Atom1927 PredecessorHalfFin13Atom1952 PredecessorHalfFin13Atom1987
    PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2046 PredecessorHalfFin13Atom2053
    PredecessorHalfFin13Atom2078 PredecessorHalfFin13Atom2113 PredecessorHalfFin13Atom2183 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28006 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom2044 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2184 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4796
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1844 PredecessorHalfFin13Atom1851
    PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1865 PredecessorHalfFin13Atom1872
    PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1918 PredecessorHalfFin13Atom1921
    PredecessorHalfFin13Atom1928 PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom1988
    PredecessorHalfFin13Atom2044 PredecessorHalfFin13Atom2047 PredecessorHalfFin13Atom2054
    PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2184 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28007 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom2185 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3260
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1832
    PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1843 PredecessorHalfFin13Atom1852
    PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1864 PredecessorHalfFin13Atom1873
    PredecessorHalfFin13Atom1898 PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1920
    PredecessorHalfFin13Atom1929 PredecessorHalfFin13Atom1954 PredecessorHalfFin13Atom1989
    PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2046 PredecessorHalfFin13Atom2055
    PredecessorHalfFin13Atom2080 PredecessorHalfFin13Atom2115 PredecessorHalfFin13Atom2185 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28008 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom2045 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom2186 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5308
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1844 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1865 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1899 PredecessorHalfFin13Atom1919 PredecessorHalfFin13Atom1921
    PredecessorHalfFin13Atom1930 PredecessorHalfFin13Atom1955 PredecessorHalfFin13Atom1990
    PredecessorHalfFin13Atom2045 PredecessorHalfFin13Atom2047 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2081 PredecessorHalfFin13Atom2116 PredecessorHalfFin13Atom2186 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28009 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom2046 chi ∧
      ¬PredecessorHalfFin13Atom2047 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom2187 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 7, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6332
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1828 PredecessorHalfFin13Atom1832 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1843 PredecessorHalfFin13Atom1844 PredecessorHalfFin13Atom1854
    PredecessorHalfFin13Atom1864 PredecessorHalfFin13Atom1865 PredecessorHalfFin13Atom1875
    PredecessorHalfFin13Atom1900 PredecessorHalfFin13Atom1920 PredecessorHalfFin13Atom1921
    PredecessorHalfFin13Atom1931 PredecessorHalfFin13Atom1956 PredecessorHalfFin13Atom1991
    PredecessorHalfFin13Atom2046 PredecessorHalfFin13Atom2047 PredecessorHalfFin13Atom2057
    PredecessorHalfFin13Atom2082 PredecessorHalfFin13Atom2117 PredecessorHalfFin13Atom2187 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28010 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom2188 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1852
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1831
    PredecessorHalfFin13Atom1845 PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1849
    PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1870
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1923
    PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1992
    PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2052
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2188 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28011 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom2189 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2876
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1832
    PredecessorHalfFin13Atom1845 PredecessorHalfFin13Atom1847 PredecessorHalfFin13Atom1850
    PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1868 PredecessorHalfFin13Atom1871
    PredecessorHalfFin13Atom1902 PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1924
    PredecessorHalfFin13Atom1927 PredecessorHalfFin13Atom1958 PredecessorHalfFin13Atom1993
    PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2050 PredecessorHalfFin13Atom2053
    PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2119 PredecessorHalfFin13Atom2189 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28012 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom2048 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom2190 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4924
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1845 PredecessorHalfFin13Atom1848 PredecessorHalfFin13Atom1851
    PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1869 PredecessorHalfFin13Atom1872
    PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1922 PredecessorHalfFin13Atom1925
    PredecessorHalfFin13Atom1928 PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom1994
    PredecessorHalfFin13Atom2048 PredecessorHalfFin13Atom2051 PredecessorHalfFin13Atom2054
    PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2190 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28013 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom2191 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3388
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1832
    PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1847 PredecessorHalfFin13Atom1852
    PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1868 PredecessorHalfFin13Atom1873
    PredecessorHalfFin13Atom1904 PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1924
    PredecessorHalfFin13Atom1929 PredecessorHalfFin13Atom1960 PredecessorHalfFin13Atom1995
    PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2050 PredecessorHalfFin13Atom2055
    PredecessorHalfFin13Atom2086 PredecessorHalfFin13Atom2121 PredecessorHalfFin13Atom2191 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28014 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom2049 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom2192 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5436
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1848 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1869 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom1923 PredecessorHalfFin13Atom1925
    PredecessorHalfFin13Atom1930 PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom1996
    PredecessorHalfFin13Atom2049 PredecessorHalfFin13Atom2051 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2192 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28015 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom1997 chi ∧
      ¬PredecessorHalfFin13Atom2050 chi ∧
      ¬PredecessorHalfFin13Atom2051 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom2193 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 8, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6460
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1829 PredecessorHalfFin13Atom1832 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1847 PredecessorHalfFin13Atom1848 PredecessorHalfFin13Atom1854
    PredecessorHalfFin13Atom1868 PredecessorHalfFin13Atom1869 PredecessorHalfFin13Atom1875
    PredecessorHalfFin13Atom1906 PredecessorHalfFin13Atom1924 PredecessorHalfFin13Atom1925
    PredecessorHalfFin13Atom1931 PredecessorHalfFin13Atom1962 PredecessorHalfFin13Atom1997
    PredecessorHalfFin13Atom2050 PredecessorHalfFin13Atom2051 PredecessorHalfFin13Atom2057
    PredecessorHalfFin13Atom2088 PredecessorHalfFin13Atom2123 PredecessorHalfFin13Atom2193 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28016 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom1998 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom2194 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3644
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1832
    PredecessorHalfFin13Atom1849 PredecessorHalfFin13Atom1850 PredecessorHalfFin13Atom1852
    PredecessorHalfFin13Atom1870 PredecessorHalfFin13Atom1871 PredecessorHalfFin13Atom1873
    PredecessorHalfFin13Atom1907 PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1927
    PredecessorHalfFin13Atom1929 PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom1998
    PredecessorHalfFin13Atom2052 PredecessorHalfFin13Atom2053 PredecessorHalfFin13Atom2055
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2194 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28017 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom1999 chi ∧
      ¬PredecessorHalfFin13Atom2052 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom2195 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5692
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1849 PredecessorHalfFin13Atom1851 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1870 PredecessorHalfFin13Atom1872 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom1926 PredecessorHalfFin13Atom1928
    PredecessorHalfFin13Atom1930 PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom1999
    PredecessorHalfFin13Atom2052 PredecessorHalfFin13Atom2054 PredecessorHalfFin13Atom2056
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2195 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28018 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom2000 chi ∧
      ¬PredecessorHalfFin13Atom2053 chi ∧
      ¬PredecessorHalfFin13Atom2054 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom2196 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6716
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1830 PredecessorHalfFin13Atom1832 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1850 PredecessorHalfFin13Atom1851 PredecessorHalfFin13Atom1854
    PredecessorHalfFin13Atom1871 PredecessorHalfFin13Atom1872 PredecessorHalfFin13Atom1875
    PredecessorHalfFin13Atom1909 PredecessorHalfFin13Atom1927 PredecessorHalfFin13Atom1928
    PredecessorHalfFin13Atom1931 PredecessorHalfFin13Atom1965 PredecessorHalfFin13Atom2000
    PredecessorHalfFin13Atom2053 PredecessorHalfFin13Atom2054 PredecessorHalfFin13Atom2057
    PredecessorHalfFin13Atom2091 PredecessorHalfFin13Atom2126 PredecessorHalfFin13Atom2196 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28019 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom2001 chi ∧
      ¬PredecessorHalfFin13Atom2055 chi ∧
      ¬PredecessorHalfFin13Atom2056 chi ∧
      ¬PredecessorHalfFin13Atom2057 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom2197 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 5, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7228
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1831 PredecessorHalfFin13Atom1832 PredecessorHalfFin13Atom1833
    PredecessorHalfFin13Atom1852 PredecessorHalfFin13Atom1853 PredecessorHalfFin13Atom1854
    PredecessorHalfFin13Atom1873 PredecessorHalfFin13Atom1874 PredecessorHalfFin13Atom1875
    PredecessorHalfFin13Atom1910 PredecessorHalfFin13Atom1929 PredecessorHalfFin13Atom1930
    PredecessorHalfFin13Atom1931 PredecessorHalfFin13Atom1966 PredecessorHalfFin13Atom2001
    PredecessorHalfFin13Atom2055 PredecessorHalfFin13Atom2056 PredecessorHalfFin13Atom2057
    PredecessorHalfFin13Atom2092 PredecessorHalfFin13Atom2127 PredecessorHalfFin13Atom2197 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28020 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2198 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask0988
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1836
    PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1845
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1881
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1933
    PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom2002
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2063
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2198 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28021 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2199 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1500
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1837
    PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1846
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1882
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1934
    PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom2003
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2064
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2199 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28022 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2200 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 8, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2524
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1838
    PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1843 PredecessorHalfFin13Atom1847
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1879 PredecessorHalfFin13Atom1883
    PredecessorHalfFin13Atom1893 PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1935
    PredecessorHalfFin13Atom1939 PredecessorHalfFin13Atom1949 PredecessorHalfFin13Atom2004
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2061 PredecessorHalfFin13Atom2065
    PredecessorHalfFin13Atom2075 PredecessorHalfFin13Atom2130 PredecessorHalfFin13Atom2200 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28023 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2058 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2201 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4572
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1839
    PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1844 PredecessorHalfFin13Atom1848
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1884
    PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1932 PredecessorHalfFin13Atom1936
    PredecessorHalfFin13Atom1940 PredecessorHalfFin13Atom1950 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2058 PredecessorHalfFin13Atom2062 PredecessorHalfFin13Atom2066
    PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2131 PredecessorHalfFin13Atom2201 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28024 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2202 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1756
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1837
    PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1849
    PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1885
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1934
    PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom2006
    PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2067
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2202 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28025 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2203 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2780
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1838
    PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1843 PredecessorHalfFin13Atom1850
    PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1879 PredecessorHalfFin13Atom1886
    PredecessorHalfFin13Atom1896 PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1935
    PredecessorHalfFin13Atom1942 PredecessorHalfFin13Atom1952 PredecessorHalfFin13Atom2007
    PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2061 PredecessorHalfFin13Atom2068
    PredecessorHalfFin13Atom2078 PredecessorHalfFin13Atom2133 PredecessorHalfFin13Atom2203 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28026 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2059 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2204 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4828
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1839
    PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1844 PredecessorHalfFin13Atom1851
    PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1887
    PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1933 PredecessorHalfFin13Atom1936
    PredecessorHalfFin13Atom1943 PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom2008
    PredecessorHalfFin13Atom2059 PredecessorHalfFin13Atom2062 PredecessorHalfFin13Atom2069
    PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2134 PredecessorHalfFin13Atom2204 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28027 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom2009 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2061 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom2205 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3292
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1838
    PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1843 PredecessorHalfFin13Atom1852
    PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1879 PredecessorHalfFin13Atom1888
    PredecessorHalfFin13Atom1898 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1935
    PredecessorHalfFin13Atom1944 PredecessorHalfFin13Atom1954 PredecessorHalfFin13Atom2009
    PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2061 PredecessorHalfFin13Atom2070
    PredecessorHalfFin13Atom2080 PredecessorHalfFin13Atom2135 PredecessorHalfFin13Atom2205 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28028 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom2010 chi ∧
      ¬PredecessorHalfFin13Atom2060 chi ∧
      ¬PredecessorHalfFin13Atom2062 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom2206 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5340
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1834 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1839
    PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1844 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1899 PredecessorHalfFin13Atom1934 PredecessorHalfFin13Atom1936
    PredecessorHalfFin13Atom1945 PredecessorHalfFin13Atom1955 PredecessorHalfFin13Atom2010
    PredecessorHalfFin13Atom2060 PredecessorHalfFin13Atom2062 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2081 PredecessorHalfFin13Atom2136 PredecessorHalfFin13Atom2206 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28030 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom2012 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom2208 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1884
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1837
    PredecessorHalfFin13Atom1845 PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1849
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1885
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1938
    PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom2012
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2067
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2208 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28032 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom2014 chi ∧
      ¬PredecessorHalfFin13Atom2063 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom2210 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4956
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1839
    PredecessorHalfFin13Atom1845 PredecessorHalfFin13Atom1848 PredecessorHalfFin13Atom1851
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1887
    PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1937 PredecessorHalfFin13Atom1940
    PredecessorHalfFin13Atom1943 PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom2014
    PredecessorHalfFin13Atom2063 PredecessorHalfFin13Atom2066 PredecessorHalfFin13Atom2069
    PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2140 PredecessorHalfFin13Atom2210 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28033 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom2015 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2065 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom2211 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3420
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1838
    PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1847 PredecessorHalfFin13Atom1852
    PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1883 PredecessorHalfFin13Atom1888
    PredecessorHalfFin13Atom1904 PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1939
    PredecessorHalfFin13Atom1944 PredecessorHalfFin13Atom1960 PredecessorHalfFin13Atom2015
    PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2065 PredecessorHalfFin13Atom2070
    PredecessorHalfFin13Atom2086 PredecessorHalfFin13Atom2141 PredecessorHalfFin13Atom2211 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28034 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom2016 chi ∧
      ¬PredecessorHalfFin13Atom2064 chi ∧
      ¬PredecessorHalfFin13Atom2066 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom2212 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5468
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1835 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1839
    PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1848 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom1938 PredecessorHalfFin13Atom1940
    PredecessorHalfFin13Atom1945 PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom2016
    PredecessorHalfFin13Atom2064 PredecessorHalfFin13Atom2066 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2212 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28036 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1838 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1888 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom2018 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2068 chi ∧
      ¬PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom2214 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3676
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1838
    PredecessorHalfFin13Atom1849 PredecessorHalfFin13Atom1850 PredecessorHalfFin13Atom1852
    PredecessorHalfFin13Atom1885 PredecessorHalfFin13Atom1886 PredecessorHalfFin13Atom1888
    PredecessorHalfFin13Atom1907 PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1942
    PredecessorHalfFin13Atom1944 PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom2018
    PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2068 PredecessorHalfFin13Atom2070
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2144 PredecessorHalfFin13Atom2214 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28037 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom1839 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1889 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2019 chi ∧
      ¬PredecessorHalfFin13Atom2067 chi ∧
      ¬PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom2215 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5724
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1836 PredecessorHalfFin13Atom1837 PredecessorHalfFin13Atom1839
    PredecessorHalfFin13Atom1849 PredecessorHalfFin13Atom1851 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1885 PredecessorHalfFin13Atom1887 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom1941 PredecessorHalfFin13Atom1943
    PredecessorHalfFin13Atom1945 PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom2019
    PredecessorHalfFin13Atom2067 PredecessorHalfFin13Atom2069 PredecessorHalfFin13Atom2071
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2215 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28040 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom2022 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom2218 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1948
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1842
    PredecessorHalfFin13Atom1845 PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1849
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1895
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1948
    PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom2022
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2077
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2218 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28041 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1902 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom2023 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom2219 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2972
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1843
    PredecessorHalfFin13Atom1845 PredecessorHalfFin13Atom1847 PredecessorHalfFin13Atom1850
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1893 PredecessorHalfFin13Atom1896
    PredecessorHalfFin13Atom1902 PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1949
    PredecessorHalfFin13Atom1952 PredecessorHalfFin13Atom1958 PredecessorHalfFin13Atom2023
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2075 PredecessorHalfFin13Atom2078
    PredecessorHalfFin13Atom2084 PredecessorHalfFin13Atom2149 PredecessorHalfFin13Atom2219 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28042 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom2024 chi ∧
      ¬PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom2220 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5020
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1844
    PredecessorHalfFin13Atom1845 PredecessorHalfFin13Atom1848 PredecessorHalfFin13Atom1851
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1897
    PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1947 PredecessorHalfFin13Atom1950
    PredecessorHalfFin13Atom1953 PredecessorHalfFin13Atom1959 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2073 PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2079
    PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2150 PredecessorHalfFin13Atom2220 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28043 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom2025 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom2221 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3484
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1843
    PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1847 PredecessorHalfFin13Atom1852
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1893 PredecessorHalfFin13Atom1898
    PredecessorHalfFin13Atom1904 PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1949
    PredecessorHalfFin13Atom1954 PredecessorHalfFin13Atom1960 PredecessorHalfFin13Atom2025
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2075 PredecessorHalfFin13Atom2080
    PredecessorHalfFin13Atom2086 PredecessorHalfFin13Atom2151 PredecessorHalfFin13Atom2221 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28044 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1840 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom2026 chi ∧
      ¬PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom2222 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5532
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1840 PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1844
    PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1848 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1899
    PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom1948 PredecessorHalfFin13Atom1950
    PredecessorHalfFin13Atom1955 PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom2026
    PredecessorHalfFin13Atom2074 PredecessorHalfFin13Atom2076 PredecessorHalfFin13Atom2081
    PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2152 PredecessorHalfFin13Atom2222 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28046 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1850 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom2028 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom2224 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3740
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1843
    PredecessorHalfFin13Atom1849 PredecessorHalfFin13Atom1850 PredecessorHalfFin13Atom1852
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1896 PredecessorHalfFin13Atom1898
    PredecessorHalfFin13Atom1907 PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1952
    PredecessorHalfFin13Atom1954 PredecessorHalfFin13Atom1963 PredecessorHalfFin13Atom2028
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2078 PredecessorHalfFin13Atom2080
    PredecessorHalfFin13Atom2089 PredecessorHalfFin13Atom2154 PredecessorHalfFin13Atom2224 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28047 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1841 chi ∧
      ¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2029 chi ∧
      ¬PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom2225 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5788
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1841 PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1844
    PredecessorHalfFin13Atom1849 PredecessorHalfFin13Atom1851 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1899
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom1951 PredecessorHalfFin13Atom1953
    PredecessorHalfFin13Atom1955 PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom2029
    PredecessorHalfFin13Atom2077 PredecessorHalfFin13Atom2079 PredecessorHalfFin13Atom2081
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2225 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28049 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1842 chi ∧
      ¬PredecessorHalfFin13Atom1843 chi ∧
      ¬PredecessorHalfFin13Atom1844 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1898 chi ∧
      ¬PredecessorHalfFin13Atom1899 chi ∧
      ¬PredecessorHalfFin13Atom1900 chi ∧
      ¬PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom2031 chi ∧
      ¬PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom2227 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 7, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7324
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1842 PredecessorHalfFin13Atom1843 PredecessorHalfFin13Atom1844
    PredecessorHalfFin13Atom1852 PredecessorHalfFin13Atom1853 PredecessorHalfFin13Atom1854
    PredecessorHalfFin13Atom1898 PredecessorHalfFin13Atom1899 PredecessorHalfFin13Atom1900
    PredecessorHalfFin13Atom1910 PredecessorHalfFin13Atom1954 PredecessorHalfFin13Atom1955
    PredecessorHalfFin13Atom1956 PredecessorHalfFin13Atom1966 PredecessorHalfFin13Atom2031
    PredecessorHalfFin13Atom2080 PredecessorHalfFin13Atom2081 PredecessorHalfFin13Atom2082
    PredecessorHalfFin13Atom2092 PredecessorHalfFin13Atom2157 PredecessorHalfFin13Atom2227 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28051 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1845 chi ∧
      ¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1849 chi ∧
      ¬PredecessorHalfFin13Atom1851 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1901 chi ∧
      ¬PredecessorHalfFin13Atom1903 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom2033 chi ∧
      ¬PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom2229 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5916
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1845 PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1848
    PredecessorHalfFin13Atom1849 PredecessorHalfFin13Atom1851 PredecessorHalfFin13Atom1853
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1905
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom1957 PredecessorHalfFin13Atom1959
    PredecessorHalfFin13Atom1961 PredecessorHalfFin13Atom1964 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2083 PredecessorHalfFin13Atom2085 PredecessorHalfFin13Atom2087
    PredecessorHalfFin13Atom2090 PredecessorHalfFin13Atom2159 PredecessorHalfFin13Atom2229 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28053 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1846 chi ∧
      ¬PredecessorHalfFin13Atom1847 chi ∧
      ¬PredecessorHalfFin13Atom1848 chi ∧
      ¬PredecessorHalfFin13Atom1852 chi ∧
      ¬PredecessorHalfFin13Atom1853 chi ∧
      ¬PredecessorHalfFin13Atom1854 chi ∧
      ¬PredecessorHalfFin13Atom1904 chi ∧
      ¬PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom2035 chi ∧
      ¬PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom2231 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 4, 8, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7452
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1846 PredecessorHalfFin13Atom1847 PredecessorHalfFin13Atom1848
    PredecessorHalfFin13Atom1852 PredecessorHalfFin13Atom1853 PredecessorHalfFin13Atom1854
    PredecessorHalfFin13Atom1904 PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom1906
    PredecessorHalfFin13Atom1910 PredecessorHalfFin13Atom1960 PredecessorHalfFin13Atom1961
    PredecessorHalfFin13Atom1962 PredecessorHalfFin13Atom1966 PredecessorHalfFin13Atom2035
    PredecessorHalfFin13Atom2086 PredecessorHalfFin13Atom2087 PredecessorHalfFin13Atom2088
    PredecessorHalfFin13Atom2092 PredecessorHalfFin13Atom2161 PredecessorHalfFin13Atom2231 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28055 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom1891 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom2002 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom2233 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 8, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1004
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1857
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1866
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1881
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1968
    PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom2002
    PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2098
    PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2233 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28056 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1882 chi ∧
      ¬PredecessorHalfFin13Atom1892 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom2003 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom2234 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 8, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1516
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1858
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1867
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1882
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1969
    PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom2003
    PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2099
    PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2234 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28057 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1883 chi ∧
      ¬PredecessorHalfFin13Atom1893 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom2004 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom2235 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 8, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2540
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1859
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1864 PredecessorHalfFin13Atom1868
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1879 PredecessorHalfFin13Atom1883
    PredecessorHalfFin13Atom1893 PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1970
    PredecessorHalfFin13Atom1974 PredecessorHalfFin13Atom1984 PredecessorHalfFin13Atom2004
    PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2096 PredecessorHalfFin13Atom2100
    PredecessorHalfFin13Atom2110 PredecessorHalfFin13Atom2130 PredecessorHalfFin13Atom2235 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28058 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1856 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1884 chi ∧
      ¬PredecessorHalfFin13Atom1894 chi ∧
      ¬PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom2005 chi ∧
      ¬PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom2236 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 8, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4588
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1860
    PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1865 PredecessorHalfFin13Atom1869
    PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1884
    PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1967 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1975 PredecessorHalfFin13Atom1985 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2093 PredecessorHalfFin13Atom2097 PredecessorHalfFin13Atom2101
    PredecessorHalfFin13Atom2111 PredecessorHalfFin13Atom2131 PredecessorHalfFin13Atom2236 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28059 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1858 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom1885 chi ∧
      ¬PredecessorHalfFin13Atom1895 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom2006 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom2237 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1772
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1858
    PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1870
    PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1885
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1969
    PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom2006
    PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2102
    PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2132 PredecessorHalfFin13Atom2237 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28060 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom1886 chi ∧
      ¬PredecessorHalfFin13Atom1896 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom2007 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom2238 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2796
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1859
    PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1864 PredecessorHalfFin13Atom1871
    PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1879 PredecessorHalfFin13Atom1886
    PredecessorHalfFin13Atom1896 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1970
    PredecessorHalfFin13Atom1977 PredecessorHalfFin13Atom1987 PredecessorHalfFin13Atom2007
    PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2096 PredecessorHalfFin13Atom2103
    PredecessorHalfFin13Atom2113 PredecessorHalfFin13Atom2133 PredecessorHalfFin13Atom2238 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28061 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1855 chi ∧
      ¬PredecessorHalfFin13Atom1857 chi ∧
      ¬PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom1887 chi ∧
      ¬PredecessorHalfFin13Atom1897 chi ∧
      ¬PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom2008 chi ∧
      ¬PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom2239 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4844
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1860
    PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1865 PredecessorHalfFin13Atom1872
    PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1887
    PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1968 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1978 PredecessorHalfFin13Atom1988 PredecessorHalfFin13Atom2008
    PredecessorHalfFin13Atom2094 PredecessorHalfFin13Atom2097 PredecessorHalfFin13Atom2104
    PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2134 PredecessorHalfFin13Atom2239 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28062 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1855 chi ∧
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
      ¬PredecessorHalfFin13Atom2240 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3308
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1859
    PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1864 PredecessorHalfFin13Atom1873
    PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1879 PredecessorHalfFin13Atom1888
    PredecessorHalfFin13Atom1898 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1970
    PredecessorHalfFin13Atom1979 PredecessorHalfFin13Atom1989 PredecessorHalfFin13Atom2009
    PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2096 PredecessorHalfFin13Atom2105
    PredecessorHalfFin13Atom2115 PredecessorHalfFin13Atom2135 PredecessorHalfFin13Atom2240 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28063 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1855 chi ∧
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
      ¬PredecessorHalfFin13Atom2241 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5356
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1855 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1860
    PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1865 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1880 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1899 PredecessorHalfFin13Atom1969 PredecessorHalfFin13Atom1971
    PredecessorHalfFin13Atom1980 PredecessorHalfFin13Atom1990 PredecessorHalfFin13Atom2010
    PredecessorHalfFin13Atom2095 PredecessorHalfFin13Atom2097 PredecessorHalfFin13Atom2106
    PredecessorHalfFin13Atom2116 PredecessorHalfFin13Atom2136 PredecessorHalfFin13Atom2241 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28065 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1856 chi ∧
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
      ¬PredecessorHalfFin13Atom2243 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1900
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1858
    PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1870
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1885
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1973
    PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom2012
    PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2102
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2243 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28066 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1856 chi ∧
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
      ¬PredecessorHalfFin13Atom2244 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask2924
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1859
    PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1868 PredecessorHalfFin13Atom1871
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1883 PredecessorHalfFin13Atom1886
    PredecessorHalfFin13Atom1902 PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1974
    PredecessorHalfFin13Atom1977 PredecessorHalfFin13Atom1993 PredecessorHalfFin13Atom2013
    PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2100 PredecessorHalfFin13Atom2103
    PredecessorHalfFin13Atom2119 PredecessorHalfFin13Atom2139 PredecessorHalfFin13Atom2244 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28067 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1856 chi ∧
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
      ¬PredecessorHalfFin13Atom2245 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask4972
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1860
    PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1869 PredecessorHalfFin13Atom1872
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1887
    PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1972 PredecessorHalfFin13Atom1975
    PredecessorHalfFin13Atom1978 PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom2014
    PredecessorHalfFin13Atom2098 PredecessorHalfFin13Atom2101 PredecessorHalfFin13Atom2104
    PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2140 PredecessorHalfFin13Atom2245 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28068 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1856 chi ∧
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
      ¬PredecessorHalfFin13Atom2246 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3436
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1859
    PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1868 PredecessorHalfFin13Atom1873
    PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1883 PredecessorHalfFin13Atom1888
    PredecessorHalfFin13Atom1904 PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1974
    PredecessorHalfFin13Atom1979 PredecessorHalfFin13Atom1995 PredecessorHalfFin13Atom2015
    PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2100 PredecessorHalfFin13Atom2105
    PredecessorHalfFin13Atom2121 PredecessorHalfFin13Atom2141 PredecessorHalfFin13Atom2246 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28069 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1856 chi ∧
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
      ¬PredecessorHalfFin13Atom2247 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5484
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1860
    PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1869 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom1973 PredecessorHalfFin13Atom1975
    PredecessorHalfFin13Atom1980 PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom2016
    PredecessorHalfFin13Atom2099 PredecessorHalfFin13Atom2101 PredecessorHalfFin13Atom2106
    PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2247 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28070 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1856 chi ∧
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
      ¬PredecessorHalfFin13Atom2248 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 8, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6508
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1856 PredecessorHalfFin13Atom1859 PredecessorHalfFin13Atom1860
    PredecessorHalfFin13Atom1868 PredecessorHalfFin13Atom1869 PredecessorHalfFin13Atom1875
    PredecessorHalfFin13Atom1883 PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1890
    PredecessorHalfFin13Atom1906 PredecessorHalfFin13Atom1974 PredecessorHalfFin13Atom1975
    PredecessorHalfFin13Atom1981 PredecessorHalfFin13Atom1997 PredecessorHalfFin13Atom2017
    PredecessorHalfFin13Atom2100 PredecessorHalfFin13Atom2101 PredecessorHalfFin13Atom2107
    PredecessorHalfFin13Atom2123 PredecessorHalfFin13Atom2143 PredecessorHalfFin13Atom2248 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28071 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1857 chi ∧
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
      ¬PredecessorHalfFin13Atom2249 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3692
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1859
    PredecessorHalfFin13Atom1870 PredecessorHalfFin13Atom1871 PredecessorHalfFin13Atom1873
    PredecessorHalfFin13Atom1885 PredecessorHalfFin13Atom1886 PredecessorHalfFin13Atom1888
    PredecessorHalfFin13Atom1907 PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1977
    PredecessorHalfFin13Atom1979 PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom2018
    PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2103 PredecessorHalfFin13Atom2105
    PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2144 PredecessorHalfFin13Atom2249 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28072 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1857 chi ∧
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
      ¬PredecessorHalfFin13Atom2250 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5740
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1857 PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1860
    PredecessorHalfFin13Atom1870 PredecessorHalfFin13Atom1872 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1885 PredecessorHalfFin13Atom1887 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom1976 PredecessorHalfFin13Atom1978
    PredecessorHalfFin13Atom1980 PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2019
    PredecessorHalfFin13Atom2102 PredecessorHalfFin13Atom2104 PredecessorHalfFin13Atom2106
    PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2145 PredecessorHalfFin13Atom2250 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28074 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1858 chi ∧
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
      ¬PredecessorHalfFin13Atom2252 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 6, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7276
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1858 PredecessorHalfFin13Atom1859 PredecessorHalfFin13Atom1860
    PredecessorHalfFin13Atom1873 PredecessorHalfFin13Atom1874 PredecessorHalfFin13Atom1875
    PredecessorHalfFin13Atom1888 PredecessorHalfFin13Atom1889 PredecessorHalfFin13Atom1890
    PredecessorHalfFin13Atom1910 PredecessorHalfFin13Atom1979 PredecessorHalfFin13Atom1980
    PredecessorHalfFin13Atom1981 PredecessorHalfFin13Atom2001 PredecessorHalfFin13Atom2021
    PredecessorHalfFin13Atom2105 PredecessorHalfFin13Atom2106 PredecessorHalfFin13Atom2107
    PredecessorHalfFin13Atom2127 PredecessorHalfFin13Atom2147 PredecessorHalfFin13Atom2252 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28075 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1861 chi ∧
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
      ¬PredecessorHalfFin13Atom2253 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1964
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1863
    PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1870
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1895
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1983
    PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom2022
    PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2112
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2253 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28077 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1861 chi ∧
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
      ¬PredecessorHalfFin13Atom2255 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5036
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1865
    PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1869 PredecessorHalfFin13Atom1872
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1897
    PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1982 PredecessorHalfFin13Atom1985
    PredecessorHalfFin13Atom1988 PredecessorHalfFin13Atom1994 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2108 PredecessorHalfFin13Atom2111 PredecessorHalfFin13Atom2114
    PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2150 PredecessorHalfFin13Atom2255 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28078 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1861 chi ∧
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
      ¬PredecessorHalfFin13Atom2256 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 7, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3500
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1864
    PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1868 PredecessorHalfFin13Atom1873
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1893 PredecessorHalfFin13Atom1898
    PredecessorHalfFin13Atom1904 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom1984
    PredecessorHalfFin13Atom1989 PredecessorHalfFin13Atom1995 PredecessorHalfFin13Atom2025
    PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2110 PredecessorHalfFin13Atom2115
    PredecessorHalfFin13Atom2121 PredecessorHalfFin13Atom2151 PredecessorHalfFin13Atom2256 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28079 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1861 chi ∧
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
      ¬PredecessorHalfFin13Atom2257 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5548
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1861 PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1865
    PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1869 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1899
    PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom1983 PredecessorHalfFin13Atom1985
    PredecessorHalfFin13Atom1990 PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom2026
    PredecessorHalfFin13Atom2109 PredecessorHalfFin13Atom2111 PredecessorHalfFin13Atom2116
    PredecessorHalfFin13Atom2122 PredecessorHalfFin13Atom2152 PredecessorHalfFin13Atom2257 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28081 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1862 chi ∧
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
      ¬PredecessorHalfFin13Atom2259 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 7, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3756
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1864
    PredecessorHalfFin13Atom1870 PredecessorHalfFin13Atom1871 PredecessorHalfFin13Atom1873
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1896 PredecessorHalfFin13Atom1898
    PredecessorHalfFin13Atom1907 PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1987
    PredecessorHalfFin13Atom1989 PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom2028
    PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2113 PredecessorHalfFin13Atom2115
    PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2154 PredecessorHalfFin13Atom2259 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28082 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1862 chi ∧
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
      ¬PredecessorHalfFin13Atom2260 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 7, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5804
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1865
    PredecessorHalfFin13Atom1870 PredecessorHalfFin13Atom1872 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1895 PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1899
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom1986 PredecessorHalfFin13Atom1988
    PredecessorHalfFin13Atom1990 PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2029
    PredecessorHalfFin13Atom2112 PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2116
    PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2155 PredecessorHalfFin13Atom2260 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28083 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1862 chi ∧
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
      ¬PredecessorHalfFin13Atom2261 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 7, 9, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6828
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1862 PredecessorHalfFin13Atom1864 PredecessorHalfFin13Atom1865
    PredecessorHalfFin13Atom1871 PredecessorHalfFin13Atom1872 PredecessorHalfFin13Atom1875
    PredecessorHalfFin13Atom1896 PredecessorHalfFin13Atom1897 PredecessorHalfFin13Atom1900
    PredecessorHalfFin13Atom1909 PredecessorHalfFin13Atom1987 PredecessorHalfFin13Atom1988
    PredecessorHalfFin13Atom1991 PredecessorHalfFin13Atom2000 PredecessorHalfFin13Atom2030
    PredecessorHalfFin13Atom2113 PredecessorHalfFin13Atom2114 PredecessorHalfFin13Atom2117
    PredecessorHalfFin13Atom2126 PredecessorHalfFin13Atom2156 PredecessorHalfFin13Atom2261 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28084 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1863 chi ∧
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
      ¬PredecessorHalfFin13Atom2262 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 7, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7340
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1863 PredecessorHalfFin13Atom1864 PredecessorHalfFin13Atom1865
    PredecessorHalfFin13Atom1873 PredecessorHalfFin13Atom1874 PredecessorHalfFin13Atom1875
    PredecessorHalfFin13Atom1898 PredecessorHalfFin13Atom1899 PredecessorHalfFin13Atom1900
    PredecessorHalfFin13Atom1910 PredecessorHalfFin13Atom1989 PredecessorHalfFin13Atom1990
    PredecessorHalfFin13Atom1991 PredecessorHalfFin13Atom2001 PredecessorHalfFin13Atom2031
    PredecessorHalfFin13Atom2115 PredecessorHalfFin13Atom2116 PredecessorHalfFin13Atom2117
    PredecessorHalfFin13Atom2127 PredecessorHalfFin13Atom2157 PredecessorHalfFin13Atom2262 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28085 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1866 chi ∧
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
      ¬PredecessorHalfFin13Atom2263 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 8, 9, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3884
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1868
    PredecessorHalfFin13Atom1870 PredecessorHalfFin13Atom1871 PredecessorHalfFin13Atom1873
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1902 PredecessorHalfFin13Atom1904
    PredecessorHalfFin13Atom1907 PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom1993
    PredecessorHalfFin13Atom1995 PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom2032
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2119 PredecessorHalfFin13Atom2121
    PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2158 PredecessorHalfFin13Atom2263 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28086 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1866 chi ∧
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
      ¬PredecessorHalfFin13Atom2264 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 8, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5932
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1866 PredecessorHalfFin13Atom1867 PredecessorHalfFin13Atom1869
    PredecessorHalfFin13Atom1870 PredecessorHalfFin13Atom1872 PredecessorHalfFin13Atom1874
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom1905
    PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom1992 PredecessorHalfFin13Atom1994
    PredecessorHalfFin13Atom1996 PredecessorHalfFin13Atom1999 PredecessorHalfFin13Atom2033
    PredecessorHalfFin13Atom2118 PredecessorHalfFin13Atom2120 PredecessorHalfFin13Atom2122
    PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2159 PredecessorHalfFin13Atom2264 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28089 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1870 chi ∧
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
      ¬PredecessorHalfFin13Atom2267 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 5, 9, 10, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask7724
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1870 PredecessorHalfFin13Atom1871 PredecessorHalfFin13Atom1872
    PredecessorHalfFin13Atom1873 PredecessorHalfFin13Atom1874 PredecessorHalfFin13Atom1875
    PredecessorHalfFin13Atom1907 PredecessorHalfFin13Atom1908 PredecessorHalfFin13Atom1909
    PredecessorHalfFin13Atom1910 PredecessorHalfFin13Atom1998 PredecessorHalfFin13Atom1999
    PredecessorHalfFin13Atom2000 PredecessorHalfFin13Atom2001 PredecessorHalfFin13Atom2036
    PredecessorHalfFin13Atom2124 PredecessorHalfFin13Atom2125 PredecessorHalfFin13Atom2126
    PredecessorHalfFin13Atom2127 PredecessorHalfFin13Atom2162 PredecessorHalfFin13Atom2267 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28090 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1876 chi ∧
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
      ¬PredecessorHalfFin13Atom2268 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 6, 7, 8, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask1996
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1878
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1885
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1895
    PredecessorHalfFin13Atom1901 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2003
    PredecessorHalfFin13Atom2006 PredecessorHalfFin13Atom2012 PredecessorHalfFin13Atom2022
    PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2132
    PredecessorHalfFin13Atom2138 PredecessorHalfFin13Atom2148 PredecessorHalfFin13Atom2268 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28091 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1876 chi ∧
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
      ¬PredecessorHalfFin13Atom2269 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 6, 7, 8, 9, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3020
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1879
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1883 PredecessorHalfFin13Atom1886
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1893 PredecessorHalfFin13Atom1896
    PredecessorHalfFin13Atom1902 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2004
    PredecessorHalfFin13Atom2007 PredecessorHalfFin13Atom2013 PredecessorHalfFin13Atom2023
    PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2130 PredecessorHalfFin13Atom2133
    PredecessorHalfFin13Atom2139 PredecessorHalfFin13Atom2149 PredecessorHalfFin13Atom2269 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28092 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1876 chi ∧
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
      ¬PredecessorHalfFin13Atom2270 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 6, 7, 8, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5068
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1877 PredecessorHalfFin13Atom1880
    PredecessorHalfFin13Atom1881 PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1887
    PredecessorHalfFin13Atom1891 PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1897
    PredecessorHalfFin13Atom1903 PredecessorHalfFin13Atom2002 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2008 PredecessorHalfFin13Atom2014 PredecessorHalfFin13Atom2024
    PredecessorHalfFin13Atom2128 PredecessorHalfFin13Atom2131 PredecessorHalfFin13Atom2134
    PredecessorHalfFin13Atom2140 PredecessorHalfFin13Atom2150 PredecessorHalfFin13Atom2270 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28093 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1876 chi ∧
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
      ¬PredecessorHalfFin13Atom2271 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 6, 7, 8, 10, 11}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask3532
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1879
    PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1883 PredecessorHalfFin13Atom1888
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1893 PredecessorHalfFin13Atom1898
    PredecessorHalfFin13Atom1904 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2004
    PredecessorHalfFin13Atom2009 PredecessorHalfFin13Atom2015 PredecessorHalfFin13Atom2025
    PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2130 PredecessorHalfFin13Atom2135
    PredecessorHalfFin13Atom2141 PredecessorHalfFin13Atom2151 PredecessorHalfFin13Atom2271 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28094 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1876 chi ∧
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
      ¬PredecessorHalfFin13Atom2272 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 6, 7, 8, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask5580
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1878 PredecessorHalfFin13Atom1880
    PredecessorHalfFin13Atom1882 PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1889
    PredecessorHalfFin13Atom1892 PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1899
    PredecessorHalfFin13Atom1905 PredecessorHalfFin13Atom2003 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2010 PredecessorHalfFin13Atom2016 PredecessorHalfFin13Atom2026
    PredecessorHalfFin13Atom2129 PredecessorHalfFin13Atom2131 PredecessorHalfFin13Atom2136
    PredecessorHalfFin13Atom2142 PredecessorHalfFin13Atom2152 PredecessorHalfFin13Atom2272 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

theorem predecessorHalfFin13_clause28095 (chi : TripleColoring 13)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬(¬PredecessorHalfFin13Atom1876 chi ∧
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
      ¬PredecessorHalfFin13Atom2273 chi) := by
  intro hbad
  apply hno
  refine ⟨{2, 3, 6, 7, 8, 11, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := predecessorHalfFin13_fiveSubset_mask6604
    polygon hsubset hcard
  unfold PredecessorHalfFin13Atom1876 PredecessorHalfFin13Atom1879 PredecessorHalfFin13Atom1880
    PredecessorHalfFin13Atom1883 PredecessorHalfFin13Atom1884 PredecessorHalfFin13Atom1890
    PredecessorHalfFin13Atom1893 PredecessorHalfFin13Atom1894 PredecessorHalfFin13Atom1900
    PredecessorHalfFin13Atom1906 PredecessorHalfFin13Atom2004 PredecessorHalfFin13Atom2005
    PredecessorHalfFin13Atom2011 PredecessorHalfFin13Atom2017 PredecessorHalfFin13Atom2027
    PredecessorHalfFin13Atom2130 PredecessorHalfFin13Atom2131 PredecessorHalfFin13Atom2137
    PredecessorHalfFin13Atom2143 PredecessorHalfFin13Atom2153 PredecessorHalfFin13Atom2273 at hbad
  rcases heq with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 <;>
    subst polygon <;> simp_all

end ErdosSzekeres

end
