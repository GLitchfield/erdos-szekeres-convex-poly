module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 190. -/

theorem fin15Anchored_clause24320 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom1195 Fin15AnchoredAtom1199
    Fin15AnchoredAtom1309 Fin15AnchoredAtom1594 Fin15AnchoredAtom3805 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17940
  ] at hbad
  tauto

theorem fin15Anchored_clause24321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom1192 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1192 Fin15AnchoredAtom3806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06676
  ] at hbad
  tauto

theorem fin15Anchored_clause24322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom3806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06676
  ] at hbad
  tauto

theorem fin15Anchored_clause24323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom1200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1200 Fin15AnchoredAtom3806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06676
  ] at hbad
  tauto

theorem fin15Anchored_clause24324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1310 Fin15AnchoredAtom3806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06676
  ] at hbad
  tauto

theorem fin15Anchored_clause24325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1595 Fin15AnchoredAtom3806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06676
  ] at hbad
  tauto

theorem fin15Anchored_clause24326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1194 Fin15AnchoredAtom3807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10772
  ] at hbad
  tauto

theorem fin15Anchored_clause24327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1596 Fin15AnchoredAtom3807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10772
  ] at hbad
  tauto

theorem fin15Anchored_clause24328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3808 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1195 Fin15AnchoredAtom3808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18964
  ] at hbad
  tauto

theorem fin15Anchored_clause24329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom3809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12820
  ] at hbad
  tauto

theorem fin15Anchored_clause24330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1194 Fin15AnchoredAtom3809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12820
  ] at hbad
  tauto

theorem fin15Anchored_clause24331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1203 Fin15AnchoredAtom3809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12820
  ] at hbad
  tauto

theorem fin15Anchored_clause24332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1313 Fin15AnchoredAtom3809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12820
  ] at hbad
  tauto

theorem fin15Anchored_clause24333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom3809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12820
  ] at hbad
  tauto

theorem fin15Anchored_clause24334 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom1194 Fin15AnchoredAtom1203
    Fin15AnchoredAtom1313 Fin15AnchoredAtom1598 Fin15AnchoredAtom3809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12820
  ] at hbad
  tauto

theorem fin15Anchored_clause24335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom3810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21012
  ] at hbad
  tauto

theorem fin15Anchored_clause24336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1195 Fin15AnchoredAtom3810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21012
  ] at hbad
  tauto

theorem fin15Anchored_clause24337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1204 Fin15AnchoredAtom3810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21012
  ] at hbad
  tauto

theorem fin15Anchored_clause24338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1314 Fin15AnchoredAtom3810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21012
  ] at hbad
  tauto

theorem fin15Anchored_clause24339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1599 Fin15AnchoredAtom3810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21012
  ] at hbad
  tauto

theorem fin15Anchored_clause24340 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom1195 Fin15AnchoredAtom1204
    Fin15AnchoredAtom1314 Fin15AnchoredAtom1599 Fin15AnchoredAtom3810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21012
  ] at hbad
  tauto

theorem fin15Anchored_clause24341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1194 Fin15AnchoredAtom3811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25108
  ] at hbad
  tauto

theorem fin15Anchored_clause24342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1195 Fin15AnchoredAtom3811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25108
  ] at hbad
  tauto

theorem fin15Anchored_clause24343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1205 Fin15AnchoredAtom3811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25108
  ] at hbad
  tauto

theorem fin15Anchored_clause24344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1315 Fin15AnchoredAtom3811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25108
  ] at hbad
  tauto

theorem fin15Anchored_clause24345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1600 Fin15AnchoredAtom3811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25108
  ] at hbad
  tauto

theorem fin15Anchored_clause24346 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1194 Fin15AnchoredAtom1195 Fin15AnchoredAtom1205
    Fin15AnchoredAtom1315 Fin15AnchoredAtom1600 Fin15AnchoredAtom3811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25108
  ] at hbad
  tauto

theorem fin15Anchored_clause24347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3812 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom3812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07188
  ] at hbad
  tauto

theorem fin15Anchored_clause24348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3812 chi ∧
      ¬Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1316 Fin15AnchoredAtom3812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07188
  ] at hbad
  tauto

theorem fin15Anchored_clause24349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3812 chi ∧
      ¬Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1601 Fin15AnchoredAtom3812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07188
  ] at hbad
  tauto

theorem fin15Anchored_clause24350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3813 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom3813 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11284
  ] at hbad
  tauto

theorem fin15Anchored_clause24351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3813 chi ∧
      ¬Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1602 Fin15AnchoredAtom3813 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11284
  ] at hbad
  tauto

theorem fin15Anchored_clause24352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3814 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1199 Fin15AnchoredAtom3814 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19476
  ] at hbad
  tauto

theorem fin15Anchored_clause24353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom3815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13332
  ] at hbad
  tauto

theorem fin15Anchored_clause24354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom3815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13332
  ] at hbad
  tauto

theorem fin15Anchored_clause24355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1203 Fin15AnchoredAtom3815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13332
  ] at hbad
  tauto

theorem fin15Anchored_clause24356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom3815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13332
  ] at hbad
  tauto

theorem fin15Anchored_clause24357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom3815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13332
  ] at hbad
  tauto

theorem fin15Anchored_clause24358 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom1198 Fin15AnchoredAtom1203
    Fin15AnchoredAtom1319 Fin15AnchoredAtom1604 Fin15AnchoredAtom3815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13332
  ] at hbad
  tauto

theorem fin15Anchored_clause24359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom3816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21524
  ] at hbad
  tauto

theorem fin15Anchored_clause24360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1199 Fin15AnchoredAtom3816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21524
  ] at hbad
  tauto

theorem fin15Anchored_clause24361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1204 Fin15AnchoredAtom3816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21524
  ] at hbad
  tauto

theorem fin15Anchored_clause24362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1320 Fin15AnchoredAtom3816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21524
  ] at hbad
  tauto

theorem fin15Anchored_clause24363 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1605 Fin15AnchoredAtom3816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21524
  ] at hbad
  tauto

theorem fin15Anchored_clause24364 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom1199 Fin15AnchoredAtom1204
    Fin15AnchoredAtom1320 Fin15AnchoredAtom1605 Fin15AnchoredAtom3816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21524
  ] at hbad
  tauto

theorem fin15Anchored_clause24365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom3817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25620
  ] at hbad
  tauto

theorem fin15Anchored_clause24366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1199 Fin15AnchoredAtom3817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25620
  ] at hbad
  tauto

theorem fin15Anchored_clause24367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1205 Fin15AnchoredAtom3817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25620
  ] at hbad
  tauto

theorem fin15Anchored_clause24368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1321 Fin15AnchoredAtom3817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25620
  ] at hbad
  tauto

theorem fin15Anchored_clause24369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1606 Fin15AnchoredAtom3817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25620
  ] at hbad
  tauto

theorem fin15Anchored_clause24370 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom1199 Fin15AnchoredAtom1205
    Fin15AnchoredAtom1321 Fin15AnchoredAtom1606 Fin15AnchoredAtom3817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25620
  ] at hbad
  tauto

theorem fin15Anchored_clause24371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3818 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1203 Fin15AnchoredAtom3818 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14356
  ] at hbad
  tauto

theorem fin15Anchored_clause24372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3818 chi ∧
      ¬Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1322 Fin15AnchoredAtom3818 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14356
  ] at hbad
  tauto

theorem fin15Anchored_clause24373 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3818 chi ∧
      Fin15AnchoredAtom1200 chi ∧
      Fin15AnchoredAtom1201 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1322 chi ∧
      Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1200 Fin15AnchoredAtom1201 Fin15AnchoredAtom1203
    Fin15AnchoredAtom1322 Fin15AnchoredAtom1607 Fin15AnchoredAtom3818 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14356
  ] at hbad
  tauto

theorem fin15Anchored_clause24374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3819 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1204 Fin15AnchoredAtom3819 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22548
  ] at hbad
  tauto

theorem fin15Anchored_clause24375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1203 Fin15AnchoredAtom3821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28692
  ] at hbad
  tauto

theorem fin15Anchored_clause24376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1204 Fin15AnchoredAtom3821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28692
  ] at hbad
  tauto

theorem fin15Anchored_clause24377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1205 Fin15AnchoredAtom3821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28692
  ] at hbad
  tauto

theorem fin15Anchored_clause24378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1325 Fin15AnchoredAtom3821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28692
  ] at hbad
  tauto

theorem fin15Anchored_clause24379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1610 Fin15AnchoredAtom3821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28692
  ] at hbad
  tauto

theorem fin15Anchored_clause24380 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1203 Fin15AnchoredAtom1204 Fin15AnchoredAtom1205
    Fin15AnchoredAtom1325 Fin15AnchoredAtom1610 Fin15AnchoredAtom3821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28692
  ] at hbad
  tauto

theorem fin15Anchored_clause24381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom3823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00740
  ] at hbad
  tauto

theorem fin15Anchored_clause24382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom3823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00740
  ] at hbad
  tauto

theorem fin15Anchored_clause24383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom3823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00740
  ] at hbad
  tauto

theorem fin15Anchored_clause24384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom3823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00740
  ] at hbad
  tauto

theorem fin15Anchored_clause24385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom3823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00740
  ] at hbad
  tauto

theorem fin15Anchored_clause24386 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom1208 Fin15AnchoredAtom1215
    Fin15AnchoredAtom1243 Fin15AnchoredAtom1612 Fin15AnchoredAtom3823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00740
  ] at hbad
  tauto

theorem fin15Anchored_clause24387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom3824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01252
  ] at hbad
  tauto

theorem fin15Anchored_clause24388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom3824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01252
  ] at hbad
  tauto

theorem fin15Anchored_clause24389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom3824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01252
  ] at hbad
  tauto

theorem fin15Anchored_clause24390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom3824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01252
  ] at hbad
  tauto

theorem fin15Anchored_clause24391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom3824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01252
  ] at hbad
  tauto

theorem fin15Anchored_clause24392 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom1209 Fin15AnchoredAtom1216
    Fin15AnchoredAtom1244 Fin15AnchoredAtom1613 Fin15AnchoredAtom3824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01252
  ] at hbad
  tauto

theorem fin15Anchored_clause24393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom3825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02276
  ] at hbad
  tauto

theorem fin15Anchored_clause24394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1210 Fin15AnchoredAtom3825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02276
  ] at hbad
  tauto

theorem fin15Anchored_clause24395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom1217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1217 Fin15AnchoredAtom3825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02276
  ] at hbad
  tauto

theorem fin15Anchored_clause24396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom1245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1245 Fin15AnchoredAtom3825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02276
  ] at hbad
  tauto

theorem fin15Anchored_clause24397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1614 Fin15AnchoredAtom3825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02276
  ] at hbad
  tauto

theorem fin15Anchored_clause24398 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3825 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1210 chi ∧
      Fin15AnchoredAtom1217 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom1210 Fin15AnchoredAtom1217
    Fin15AnchoredAtom1245 Fin15AnchoredAtom1614 Fin15AnchoredAtom3825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02276
  ] at hbad
  tauto

theorem fin15Anchored_clause24399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom3826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04324
  ] at hbad
  tauto

theorem fin15Anchored_clause24400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom3826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04324
  ] at hbad
  tauto

theorem fin15Anchored_clause24401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom3826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04324
  ] at hbad
  tauto

theorem fin15Anchored_clause24402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom3826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04324
  ] at hbad
  tauto

theorem fin15Anchored_clause24403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom3826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04324
  ] at hbad
  tauto

theorem fin15Anchored_clause24404 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom1211 Fin15AnchoredAtom1218
    Fin15AnchoredAtom1246 Fin15AnchoredAtom1615 Fin15AnchoredAtom3826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04324
  ] at hbad
  tauto

theorem fin15Anchored_clause24405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom3827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08420
  ] at hbad
  tauto

theorem fin15Anchored_clause24406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1212 Fin15AnchoredAtom3827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08420
  ] at hbad
  tauto

theorem fin15Anchored_clause24407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1219 Fin15AnchoredAtom3827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08420
  ] at hbad
  tauto

theorem fin15Anchored_clause24408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1247 Fin15AnchoredAtom3827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08420
  ] at hbad
  tauto

theorem fin15Anchored_clause24409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom3827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08420
  ] at hbad
  tauto

theorem fin15Anchored_clause24410 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom1212 Fin15AnchoredAtom1219
    Fin15AnchoredAtom1247 Fin15AnchoredAtom1616 Fin15AnchoredAtom3827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08420
  ] at hbad
  tauto

theorem fin15Anchored_clause24411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom3828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16612
  ] at hbad
  tauto

theorem fin15Anchored_clause24412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1213 Fin15AnchoredAtom3828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16612
  ] at hbad
  tauto

theorem fin15Anchored_clause24413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1220 Fin15AnchoredAtom3828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16612
  ] at hbad
  tauto

theorem fin15Anchored_clause24414 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1248 Fin15AnchoredAtom3828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16612
  ] at hbad
  tauto

theorem fin15Anchored_clause24415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1617 Fin15AnchoredAtom3828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16612
  ] at hbad
  tauto

theorem fin15Anchored_clause24416 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom1213 Fin15AnchoredAtom1220
    Fin15AnchoredAtom1248 Fin15AnchoredAtom1617 Fin15AnchoredAtom3828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16612
  ] at hbad
  tauto

theorem fin15Anchored_clause24417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3830 chi ∧
      ¬Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1222 Fin15AnchoredAtom3830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01380
  ] at hbad
  tauto

theorem fin15Anchored_clause24418 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3830 chi ∧
      Fin15AnchoredAtom1207 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1222 chi ∧
      Fin15AnchoredAtom1250 chi ∧
      Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1207 Fin15AnchoredAtom1209 Fin15AnchoredAtom1222
    Fin15AnchoredAtom1250 Fin15AnchoredAtom1619 Fin15AnchoredAtom3830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01380
  ] at hbad
  tauto

theorem fin15Anchored_clause24419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3833 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1622 Fin15AnchoredAtom3833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08548
  ] at hbad
  tauto

theorem fin15Anchored_clause24420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom3835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01636
  ] at hbad
  tauto

theorem fin15Anchored_clause24421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom3835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01636
  ] at hbad
  tauto

theorem fin15Anchored_clause24422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom3835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01636
  ] at hbad
  tauto

theorem fin15Anchored_clause24423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom3835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01636
  ] at hbad
  tauto

theorem fin15Anchored_clause24424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom3835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01636
  ] at hbad
  tauto

theorem fin15Anchored_clause24425 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom1209 Fin15AnchoredAtom1227
    Fin15AnchoredAtom1255 Fin15AnchoredAtom1624 Fin15AnchoredAtom3835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01636
  ] at hbad
  tauto

theorem fin15Anchored_clause24426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3836 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom3836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02660
  ] at hbad
  tauto

theorem fin15Anchored_clause24427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom3837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04708
  ] at hbad
  tauto

theorem fin15Anchored_clause24428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom3837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04708
  ] at hbad
  tauto

theorem fin15Anchored_clause24429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom3837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04708
  ] at hbad
  tauto

theorem fin15Anchored_clause24430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom3837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04708
  ] at hbad
  tauto

theorem fin15Anchored_clause24431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom3837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04708
  ] at hbad
  tauto

theorem fin15Anchored_clause24432 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom1211 Fin15AnchoredAtom1229
    Fin15AnchoredAtom1257 Fin15AnchoredAtom1626 Fin15AnchoredAtom3837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04708
  ] at hbad
  tauto

theorem fin15Anchored_clause24433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom3838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08804
  ] at hbad
  tauto

theorem fin15Anchored_clause24434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1212 Fin15AnchoredAtom3838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08804
  ] at hbad
  tauto

theorem fin15Anchored_clause24435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1230 Fin15AnchoredAtom3838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08804
  ] at hbad
  tauto

theorem fin15Anchored_clause24436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1258 Fin15AnchoredAtom3838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08804
  ] at hbad
  tauto

theorem fin15Anchored_clause24437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom3838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08804
  ] at hbad
  tauto

theorem fin15Anchored_clause24438 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom1212 Fin15AnchoredAtom1230
    Fin15AnchoredAtom1258 Fin15AnchoredAtom1627 Fin15AnchoredAtom3838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08804
  ] at hbad
  tauto

theorem fin15Anchored_clause24439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom3839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16996
  ] at hbad
  tauto

theorem fin15Anchored_clause24440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1213 Fin15AnchoredAtom3839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16996
  ] at hbad
  tauto

theorem fin15Anchored_clause24441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1231 Fin15AnchoredAtom3839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16996
  ] at hbad
  tauto

theorem fin15Anchored_clause24442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1259 Fin15AnchoredAtom3839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16996
  ] at hbad
  tauto

theorem fin15Anchored_clause24443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1628 Fin15AnchoredAtom3839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16996
  ] at hbad
  tauto

theorem fin15Anchored_clause24444 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom1213 Fin15AnchoredAtom1231
    Fin15AnchoredAtom1259 Fin15AnchoredAtom1628 Fin15AnchoredAtom3839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16996
  ] at hbad
  tauto

theorem fin15Anchored_clause24445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom3840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03172
  ] at hbad
  tauto

theorem fin15Anchored_clause24446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1210 Fin15AnchoredAtom3840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03172
  ] at hbad
  tauto

theorem fin15Anchored_clause24447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1232 Fin15AnchoredAtom3840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03172
  ] at hbad
  tauto

end ErdosSzekeres

end
