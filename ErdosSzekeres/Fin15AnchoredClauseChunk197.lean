module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 197. -/

theorem fin15Anchored_clause25216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom4075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00856
  ] at hbad
  tauto

theorem fin15Anchored_clause25217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom4075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00856
  ] at hbad
  tauto

theorem fin15Anchored_clause25218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom4075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00856
  ] at hbad
  tauto

theorem fin15Anchored_clause25219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom4075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00856
  ] at hbad
  tauto

theorem fin15Anchored_clause25220 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4075 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom1337 Fin15AnchoredAtom1350
    Fin15AnchoredAtom1414 Fin15AnchoredAtom1534 Fin15AnchoredAtom4075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00856
  ] at hbad
  tauto

theorem fin15Anchored_clause25221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom4076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01368
  ] at hbad
  tauto

theorem fin15Anchored_clause25222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom4076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01368
  ] at hbad
  tauto

theorem fin15Anchored_clause25223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom4076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01368
  ] at hbad
  tauto

theorem fin15Anchored_clause25224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom4076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01368
  ] at hbad
  tauto

theorem fin15Anchored_clause25225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom4076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01368
  ] at hbad
  tauto

theorem fin15Anchored_clause25226 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom1338 Fin15AnchoredAtom1351
    Fin15AnchoredAtom1415 Fin15AnchoredAtom1535 Fin15AnchoredAtom4076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01368
  ] at hbad
  tauto

theorem fin15Anchored_clause25227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom4078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04440
  ] at hbad
  tauto

theorem fin15Anchored_clause25228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom4078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04440
  ] at hbad
  tauto

theorem fin15Anchored_clause25229 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1353 Fin15AnchoredAtom4078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04440
  ] at hbad
  tauto

theorem fin15Anchored_clause25230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1417 Fin15AnchoredAtom4078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04440
  ] at hbad
  tauto

theorem fin15Anchored_clause25231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1537 Fin15AnchoredAtom4078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04440
  ] at hbad
  tauto

theorem fin15Anchored_clause25232 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4078 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom1340 Fin15AnchoredAtom1353
    Fin15AnchoredAtom1417 Fin15AnchoredAtom1537 Fin15AnchoredAtom4078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04440
  ] at hbad
  tauto

theorem fin15Anchored_clause25233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom4079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08536
  ] at hbad
  tauto

theorem fin15Anchored_clause25234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1341 Fin15AnchoredAtom4079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08536
  ] at hbad
  tauto

theorem fin15Anchored_clause25235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1354 Fin15AnchoredAtom4079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08536
  ] at hbad
  tauto

theorem fin15Anchored_clause25236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1418 Fin15AnchoredAtom4079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08536
  ] at hbad
  tauto

theorem fin15Anchored_clause25237 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1538 Fin15AnchoredAtom4079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08536
  ] at hbad
  tauto

theorem fin15Anchored_clause25238 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4079 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom1341 Fin15AnchoredAtom1354
    Fin15AnchoredAtom1418 Fin15AnchoredAtom1538 Fin15AnchoredAtom4079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08536
  ] at hbad
  tauto

theorem fin15Anchored_clause25239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom4080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16728
  ] at hbad
  tauto

theorem fin15Anchored_clause25240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1342 Fin15AnchoredAtom4080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16728
  ] at hbad
  tauto

theorem fin15Anchored_clause25241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1355 Fin15AnchoredAtom4080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16728
  ] at hbad
  tauto

theorem fin15Anchored_clause25242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1419 Fin15AnchoredAtom4080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16728
  ] at hbad
  tauto

theorem fin15Anchored_clause25243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1539 Fin15AnchoredAtom4080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16728
  ] at hbad
  tauto

theorem fin15Anchored_clause25244 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4080 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom1342 Fin15AnchoredAtom1355
    Fin15AnchoredAtom1419 Fin15AnchoredAtom1539 Fin15AnchoredAtom4080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16728
  ] at hbad
  tauto

theorem fin15Anchored_clause25245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom4081 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01624
  ] at hbad
  tauto

theorem fin15Anchored_clause25246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom4081 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01624
  ] at hbad
  tauto

theorem fin15Anchored_clause25247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom4081 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01624
  ] at hbad
  tauto

theorem fin15Anchored_clause25248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom4081 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01624
  ] at hbad
  tauto

theorem fin15Anchored_clause25249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom4081 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01624
  ] at hbad
  tauto

theorem fin15Anchored_clause25250 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom1338 Fin15AnchoredAtom1356
    Fin15AnchoredAtom1420 Fin15AnchoredAtom1540 Fin15AnchoredAtom4081 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01624
  ] at hbad
  tauto

theorem fin15Anchored_clause25251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4082 chi ∧
      ¬Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1357 Fin15AnchoredAtom4082 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02648
  ] at hbad
  tauto

theorem fin15Anchored_clause25252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4082 chi ∧
      ¬Fin15AnchoredAtom1421 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1421 Fin15AnchoredAtom4082 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02648
  ] at hbad
  tauto

theorem fin15Anchored_clause25253 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4082 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1339 chi ∧
      Fin15AnchoredAtom1357 chi ∧
      Fin15AnchoredAtom1421 chi ∧
      Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom1339 Fin15AnchoredAtom1357
    Fin15AnchoredAtom1421 Fin15AnchoredAtom1541 Fin15AnchoredAtom4082 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02648
  ] at hbad
  tauto

theorem fin15Anchored_clause25254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom4083 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04696
  ] at hbad
  tauto

theorem fin15Anchored_clause25255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom4083 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04696
  ] at hbad
  tauto

theorem fin15Anchored_clause25256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom4083 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04696
  ] at hbad
  tauto

theorem fin15Anchored_clause25257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom4083 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04696
  ] at hbad
  tauto

theorem fin15Anchored_clause25258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom4083 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04696
  ] at hbad
  tauto

theorem fin15Anchored_clause25259 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom1340 Fin15AnchoredAtom1358
    Fin15AnchoredAtom1422 Fin15AnchoredAtom1542 Fin15AnchoredAtom4083 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04696
  ] at hbad
  tauto

theorem fin15Anchored_clause25260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom4084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08792
  ] at hbad
  tauto

theorem fin15Anchored_clause25261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1341 Fin15AnchoredAtom4084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08792
  ] at hbad
  tauto

theorem fin15Anchored_clause25262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1359 Fin15AnchoredAtom4084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08792
  ] at hbad
  tauto

theorem fin15Anchored_clause25263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom4084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08792
  ] at hbad
  tauto

theorem fin15Anchored_clause25264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom4084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08792
  ] at hbad
  tauto

theorem fin15Anchored_clause25265 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom1341 Fin15AnchoredAtom1359
    Fin15AnchoredAtom1423 Fin15AnchoredAtom1543 Fin15AnchoredAtom4084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08792
  ] at hbad
  tauto

theorem fin15Anchored_clause25266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom4085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16984
  ] at hbad
  tauto

theorem fin15Anchored_clause25267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1342 Fin15AnchoredAtom4085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16984
  ] at hbad
  tauto

theorem fin15Anchored_clause25268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1360 Fin15AnchoredAtom4085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16984
  ] at hbad
  tauto

theorem fin15Anchored_clause25269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1424 Fin15AnchoredAtom4085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16984
  ] at hbad
  tauto

theorem fin15Anchored_clause25270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1544 Fin15AnchoredAtom4085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16984
  ] at hbad
  tauto

theorem fin15Anchored_clause25271 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom1342 Fin15AnchoredAtom1360
    Fin15AnchoredAtom1424 Fin15AnchoredAtom1544 Fin15AnchoredAtom4085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16984
  ] at hbad
  tauto

theorem fin15Anchored_clause25272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4086 chi ∧
      ¬Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1425 Fin15AnchoredAtom4086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03160
  ] at hbad
  tauto

theorem fin15Anchored_clause25273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4086 chi ∧
      ¬Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1545 Fin15AnchoredAtom4086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03160
  ] at hbad
  tauto

theorem fin15Anchored_clause25274 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4086 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1339 chi ∧
      Fin15AnchoredAtom1361 chi ∧
      Fin15AnchoredAtom1425 chi ∧
      Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom1339 Fin15AnchoredAtom1361
    Fin15AnchoredAtom1425 Fin15AnchoredAtom1545 Fin15AnchoredAtom4086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03160
  ] at hbad
  tauto

theorem fin15Anchored_clause25275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom4087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05208
  ] at hbad
  tauto

theorem fin15Anchored_clause25276 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom4087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05208
  ] at hbad
  tauto

theorem fin15Anchored_clause25277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom4087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05208
  ] at hbad
  tauto

theorem fin15Anchored_clause25278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom4087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05208
  ] at hbad
  tauto

theorem fin15Anchored_clause25279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom4087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05208
  ] at hbad
  tauto

theorem fin15Anchored_clause25280 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom1340 Fin15AnchoredAtom1362
    Fin15AnchoredAtom1426 Fin15AnchoredAtom1546 Fin15AnchoredAtom4087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05208
  ] at hbad
  tauto

theorem fin15Anchored_clause25281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom4088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09304
  ] at hbad
  tauto

theorem fin15Anchored_clause25282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1341 Fin15AnchoredAtom4088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09304
  ] at hbad
  tauto

theorem fin15Anchored_clause25283 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom4088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09304
  ] at hbad
  tauto

theorem fin15Anchored_clause25284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1427 Fin15AnchoredAtom4088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09304
  ] at hbad
  tauto

theorem fin15Anchored_clause25285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom4088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09304
  ] at hbad
  tauto

theorem fin15Anchored_clause25286 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom1341 Fin15AnchoredAtom1363
    Fin15AnchoredAtom1427 Fin15AnchoredAtom1547 Fin15AnchoredAtom4088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09304
  ] at hbad
  tauto

theorem fin15Anchored_clause25287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom4089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17496
  ] at hbad
  tauto

theorem fin15Anchored_clause25288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1342 Fin15AnchoredAtom4089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17496
  ] at hbad
  tauto

theorem fin15Anchored_clause25289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1364 Fin15AnchoredAtom4089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17496
  ] at hbad
  tauto

theorem fin15Anchored_clause25290 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1428 Fin15AnchoredAtom4089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17496
  ] at hbad
  tauto

theorem fin15Anchored_clause25291 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1548 Fin15AnchoredAtom4089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17496
  ] at hbad
  tauto

theorem fin15Anchored_clause25292 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom1342 Fin15AnchoredAtom1364
    Fin15AnchoredAtom1428 Fin15AnchoredAtom1548 Fin15AnchoredAtom4089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17496
  ] at hbad
  tauto

theorem fin15Anchored_clause25293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4090 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom4090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06232
  ] at hbad
  tauto

theorem fin15Anchored_clause25294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4091 chi ∧
      ¬Fin15AnchoredAtom1430 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1430 Fin15AnchoredAtom4091 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10328
  ] at hbad
  tauto

theorem fin15Anchored_clause25295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4092 chi ∧
      ¬Fin15AnchoredAtom1367 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1367 Fin15AnchoredAtom4092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18520
  ] at hbad
  tauto

theorem fin15Anchored_clause25296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom4093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12376
  ] at hbad
  tauto

theorem fin15Anchored_clause25297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1341 Fin15AnchoredAtom4093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12376
  ] at hbad
  tauto

theorem fin15Anchored_clause25298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1368 Fin15AnchoredAtom4093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12376
  ] at hbad
  tauto

theorem fin15Anchored_clause25299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1432 Fin15AnchoredAtom4093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12376
  ] at hbad
  tauto

theorem fin15Anchored_clause25300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom4093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12376
  ] at hbad
  tauto

theorem fin15Anchored_clause25301 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom1341 Fin15AnchoredAtom1368
    Fin15AnchoredAtom1432 Fin15AnchoredAtom1552 Fin15AnchoredAtom4093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12376
  ] at hbad
  tauto

theorem fin15Anchored_clause25302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom4094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20568
  ] at hbad
  tauto

theorem fin15Anchored_clause25303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1342 Fin15AnchoredAtom4094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20568
  ] at hbad
  tauto

theorem fin15Anchored_clause25304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1369 Fin15AnchoredAtom4094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20568
  ] at hbad
  tauto

theorem fin15Anchored_clause25305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1433 Fin15AnchoredAtom4094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20568
  ] at hbad
  tauto

theorem fin15Anchored_clause25306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1553 Fin15AnchoredAtom4094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20568
  ] at hbad
  tauto

theorem fin15Anchored_clause25307 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom1342 Fin15AnchoredAtom1369
    Fin15AnchoredAtom1433 Fin15AnchoredAtom1553 Fin15AnchoredAtom4094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20568
  ] at hbad
  tauto

theorem fin15Anchored_clause25308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1341 Fin15AnchoredAtom4095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24664
  ] at hbad
  tauto

theorem fin15Anchored_clause25309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1342 Fin15AnchoredAtom4095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24664
  ] at hbad
  tauto

theorem fin15Anchored_clause25310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1370 Fin15AnchoredAtom4095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24664
  ] at hbad
  tauto

theorem fin15Anchored_clause25311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1434 Fin15AnchoredAtom4095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24664
  ] at hbad
  tauto

theorem fin15Anchored_clause25312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1554 Fin15AnchoredAtom4095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24664
  ] at hbad
  tauto

theorem fin15Anchored_clause25313 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1341 Fin15AnchoredAtom1342 Fin15AnchoredAtom1370
    Fin15AnchoredAtom1434 Fin15AnchoredAtom1554 Fin15AnchoredAtom4095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24664
  ] at hbad
  tauto

theorem fin15Anchored_clause25314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom4096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00920
  ] at hbad
  tauto

theorem fin15Anchored_clause25315 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom4096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00920
  ] at hbad
  tauto

theorem fin15Anchored_clause25316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom4096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00920
  ] at hbad
  tauto

theorem fin15Anchored_clause25317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom4096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00920
  ] at hbad
  tauto

theorem fin15Anchored_clause25318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom4096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00920
  ] at hbad
  tauto

theorem fin15Anchored_clause25319 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4096 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom1344 Fin15AnchoredAtom1350
    Fin15AnchoredAtom1435 Fin15AnchoredAtom1555 Fin15AnchoredAtom4096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00920
  ] at hbad
  tauto

theorem fin15Anchored_clause25320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom4097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01432
  ] at hbad
  tauto

theorem fin15Anchored_clause25321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom4097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01432
  ] at hbad
  tauto

theorem fin15Anchored_clause25322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom4097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01432
  ] at hbad
  tauto

theorem fin15Anchored_clause25323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom4097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01432
  ] at hbad
  tauto

theorem fin15Anchored_clause25324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom4097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01432
  ] at hbad
  tauto

theorem fin15Anchored_clause25325 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4097 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom1345 Fin15AnchoredAtom1351
    Fin15AnchoredAtom1436 Fin15AnchoredAtom1556 Fin15AnchoredAtom4097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01432
  ] at hbad
  tauto

theorem fin15Anchored_clause25326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom4099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04504
  ] at hbad
  tauto

theorem fin15Anchored_clause25327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom4099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04504
  ] at hbad
  tauto

theorem fin15Anchored_clause25328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1353 Fin15AnchoredAtom4099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04504
  ] at hbad
  tauto

theorem fin15Anchored_clause25329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1438 Fin15AnchoredAtom4099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04504
  ] at hbad
  tauto

theorem fin15Anchored_clause25330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1558 Fin15AnchoredAtom4099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04504
  ] at hbad
  tauto

theorem fin15Anchored_clause25331 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4099 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom1347 Fin15AnchoredAtom1353
    Fin15AnchoredAtom1438 Fin15AnchoredAtom1558 Fin15AnchoredAtom4099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04504
  ] at hbad
  tauto

theorem fin15Anchored_clause25332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom4100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08600
  ] at hbad
  tauto

theorem fin15Anchored_clause25333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1348 Fin15AnchoredAtom4100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08600
  ] at hbad
  tauto

theorem fin15Anchored_clause25334 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1354 Fin15AnchoredAtom4100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08600
  ] at hbad
  tauto

theorem fin15Anchored_clause25335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1439 Fin15AnchoredAtom4100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08600
  ] at hbad
  tauto

theorem fin15Anchored_clause25336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1559 Fin15AnchoredAtom4100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08600
  ] at hbad
  tauto

theorem fin15Anchored_clause25337 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4100 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom1348 Fin15AnchoredAtom1354
    Fin15AnchoredAtom1439 Fin15AnchoredAtom1559 Fin15AnchoredAtom4100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08600
  ] at hbad
  tauto

theorem fin15Anchored_clause25338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom4101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16792
  ] at hbad
  tauto

theorem fin15Anchored_clause25339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1349 Fin15AnchoredAtom4101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16792
  ] at hbad
  tauto

theorem fin15Anchored_clause25340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1355 Fin15AnchoredAtom4101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16792
  ] at hbad
  tauto

theorem fin15Anchored_clause25341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1440 Fin15AnchoredAtom4101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16792
  ] at hbad
  tauto

theorem fin15Anchored_clause25342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1560 Fin15AnchoredAtom4101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16792
  ] at hbad
  tauto

theorem fin15Anchored_clause25343 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4101 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom1349 Fin15AnchoredAtom1355
    Fin15AnchoredAtom1440 Fin15AnchoredAtom1560 Fin15AnchoredAtom4101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16792
  ] at hbad
  tauto

end ErdosSzekeres

end
