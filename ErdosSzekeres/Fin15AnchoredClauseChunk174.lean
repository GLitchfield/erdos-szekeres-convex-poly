module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 174. -/

theorem fin15Anchored_clause22272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom0972 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0972 Fin15AnchoredAtom3278 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02706
  ] at hbad
  tauto

theorem fin15Anchored_clause22273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom1057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1057 Fin15AnchoredAtom3278 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02706
  ] at hbad
  tauto

theorem fin15Anchored_clause22274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1562 Fin15AnchoredAtom3278 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02706
  ] at hbad
  tauto

theorem fin15Anchored_clause22275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom3279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04754
  ] at hbad
  tauto

theorem fin15Anchored_clause22276 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom3279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04754
  ] at hbad
  tauto

theorem fin15Anchored_clause22277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom3279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04754
  ] at hbad
  tauto

theorem fin15Anchored_clause22278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom3279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04754
  ] at hbad
  tauto

theorem fin15Anchored_clause22279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom3279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04754
  ] at hbad
  tauto

theorem fin15Anchored_clause22280 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom0962 Fin15AnchoredAtom0973
    Fin15AnchoredAtom1058 Fin15AnchoredAtom1563 Fin15AnchoredAtom3279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04754
  ] at hbad
  tauto

theorem fin15Anchored_clause22281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom3280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08850
  ] at hbad
  tauto

theorem fin15Anchored_clause22282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom3280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08850
  ] at hbad
  tauto

theorem fin15Anchored_clause22283 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom3280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08850
  ] at hbad
  tauto

theorem fin15Anchored_clause22284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom3280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08850
  ] at hbad
  tauto

theorem fin15Anchored_clause22285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom3280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08850
  ] at hbad
  tauto

theorem fin15Anchored_clause22286 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom0963 Fin15AnchoredAtom0974
    Fin15AnchoredAtom1059 Fin15AnchoredAtom1564 Fin15AnchoredAtom3280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08850
  ] at hbad
  tauto

theorem fin15Anchored_clause22287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom3281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17042
  ] at hbad
  tauto

theorem fin15Anchored_clause22288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0964 Fin15AnchoredAtom3281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17042
  ] at hbad
  tauto

theorem fin15Anchored_clause22289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0975 Fin15AnchoredAtom3281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17042
  ] at hbad
  tauto

theorem fin15Anchored_clause22290 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1060 Fin15AnchoredAtom3281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17042
  ] at hbad
  tauto

theorem fin15Anchored_clause22291 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1565 Fin15AnchoredAtom3281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17042
  ] at hbad
  tauto

theorem fin15Anchored_clause22292 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom0964 Fin15AnchoredAtom0975
    Fin15AnchoredAtom1060 Fin15AnchoredAtom1565 Fin15AnchoredAtom3281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17042
  ] at hbad
  tauto

theorem fin15Anchored_clause22293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom3282 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03218
  ] at hbad
  tauto

theorem fin15Anchored_clause22294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0961 Fin15AnchoredAtom3282 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03218
  ] at hbad
  tauto

theorem fin15Anchored_clause22295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3282 chi ∧
      ¬Fin15AnchoredAtom1061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1061 Fin15AnchoredAtom3282 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03218
  ] at hbad
  tauto

theorem fin15Anchored_clause22296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom3283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05266
  ] at hbad
  tauto

theorem fin15Anchored_clause22297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom3283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05266
  ] at hbad
  tauto

theorem fin15Anchored_clause22298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom3283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05266
  ] at hbad
  tauto

theorem fin15Anchored_clause22299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom3283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05266
  ] at hbad
  tauto

theorem fin15Anchored_clause22300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom3283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05266
  ] at hbad
  tauto

theorem fin15Anchored_clause22301 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom0962 Fin15AnchoredAtom0977
    Fin15AnchoredAtom1062 Fin15AnchoredAtom1567 Fin15AnchoredAtom3283 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05266
  ] at hbad
  tauto

theorem fin15Anchored_clause22302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom3284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09362
  ] at hbad
  tauto

theorem fin15Anchored_clause22303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom3284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09362
  ] at hbad
  tauto

theorem fin15Anchored_clause22304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0978 Fin15AnchoredAtom3284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09362
  ] at hbad
  tauto

theorem fin15Anchored_clause22305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom3284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09362
  ] at hbad
  tauto

theorem fin15Anchored_clause22306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom3284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09362
  ] at hbad
  tauto

theorem fin15Anchored_clause22307 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom0963 Fin15AnchoredAtom0978
    Fin15AnchoredAtom1063 Fin15AnchoredAtom1568 Fin15AnchoredAtom3284 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09362
  ] at hbad
  tauto

theorem fin15Anchored_clause22308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom3285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17554
  ] at hbad
  tauto

theorem fin15Anchored_clause22309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0964 Fin15AnchoredAtom3285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17554
  ] at hbad
  tauto

theorem fin15Anchored_clause22310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0979 Fin15AnchoredAtom3285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17554
  ] at hbad
  tauto

theorem fin15Anchored_clause22311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1064 Fin15AnchoredAtom3285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17554
  ] at hbad
  tauto

theorem fin15Anchored_clause22312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1569 Fin15AnchoredAtom3285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17554
  ] at hbad
  tauto

theorem fin15Anchored_clause22313 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom0964 Fin15AnchoredAtom0979
    Fin15AnchoredAtom1064 Fin15AnchoredAtom1569 Fin15AnchoredAtom3285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17554
  ] at hbad
  tauto

theorem fin15Anchored_clause22314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom3286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06290
  ] at hbad
  tauto

theorem fin15Anchored_clause22315 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom0980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0980 Fin15AnchoredAtom3286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06290
  ] at hbad
  tauto

theorem fin15Anchored_clause22316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3286 chi ∧
      ¬Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1065 Fin15AnchoredAtom3286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06290
  ] at hbad
  tauto

theorem fin15Anchored_clause22317 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3286 chi ∧
      Fin15AnchoredAtom0961 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0980 chi ∧
      Fin15AnchoredAtom1065 chi ∧
      Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0961 Fin15AnchoredAtom0962 Fin15AnchoredAtom0980
    Fin15AnchoredAtom1065 Fin15AnchoredAtom1570 Fin15AnchoredAtom3286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06290
  ] at hbad
  tauto

theorem fin15Anchored_clause22318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3287 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom3287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10386
  ] at hbad
  tauto

theorem fin15Anchored_clause22319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3287 chi ∧
      ¬Fin15AnchoredAtom0981 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0981 Fin15AnchoredAtom3287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10386
  ] at hbad
  tauto

theorem fin15Anchored_clause22320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3288 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0964 Fin15AnchoredAtom3288 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18578
  ] at hbad
  tauto

theorem fin15Anchored_clause22321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom3289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12434
  ] at hbad
  tauto

theorem fin15Anchored_clause22322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom3289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12434
  ] at hbad
  tauto

theorem fin15Anchored_clause22323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom3289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12434
  ] at hbad
  tauto

theorem fin15Anchored_clause22324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom3289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12434
  ] at hbad
  tauto

theorem fin15Anchored_clause22325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom3289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12434
  ] at hbad
  tauto

theorem fin15Anchored_clause22326 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom0963 Fin15AnchoredAtom0983
    Fin15AnchoredAtom1068 Fin15AnchoredAtom1573 Fin15AnchoredAtom3289 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12434
  ] at hbad
  tauto

theorem fin15Anchored_clause22327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom3290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20626
  ] at hbad
  tauto

theorem fin15Anchored_clause22328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0964 Fin15AnchoredAtom3290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20626
  ] at hbad
  tauto

theorem fin15Anchored_clause22329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0984 Fin15AnchoredAtom3290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20626
  ] at hbad
  tauto

theorem fin15Anchored_clause22330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1069 Fin15AnchoredAtom3290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20626
  ] at hbad
  tauto

theorem fin15Anchored_clause22331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1574 Fin15AnchoredAtom3290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20626
  ] at hbad
  tauto

theorem fin15Anchored_clause22332 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom0964 Fin15AnchoredAtom0984
    Fin15AnchoredAtom1069 Fin15AnchoredAtom1574 Fin15AnchoredAtom3290 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20626
  ] at hbad
  tauto

theorem fin15Anchored_clause22333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom3291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24722
  ] at hbad
  tauto

theorem fin15Anchored_clause22334 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0964 Fin15AnchoredAtom3291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24722
  ] at hbad
  tauto

theorem fin15Anchored_clause22335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0985 Fin15AnchoredAtom3291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24722
  ] at hbad
  tauto

theorem fin15Anchored_clause22336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1070 Fin15AnchoredAtom3291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24722
  ] at hbad
  tauto

theorem fin15Anchored_clause22337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1575 Fin15AnchoredAtom3291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24722
  ] at hbad
  tauto

theorem fin15Anchored_clause22338 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom0964 Fin15AnchoredAtom0985
    Fin15AnchoredAtom1070 Fin15AnchoredAtom1575 Fin15AnchoredAtom3291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24722
  ] at hbad
  tauto

theorem fin15Anchored_clause22339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0965 Fin15AnchoredAtom3292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01810
  ] at hbad
  tauto

theorem fin15Anchored_clause22340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom3292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01810
  ] at hbad
  tauto

theorem fin15Anchored_clause22341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom3292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01810
  ] at hbad
  tauto

theorem fin15Anchored_clause22342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1071 Fin15AnchoredAtom3292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01810
  ] at hbad
  tauto

theorem fin15Anchored_clause22343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3292 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1576 Fin15AnchoredAtom3292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01810
  ] at hbad
  tauto

theorem fin15Anchored_clause22344 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3292 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0965 Fin15AnchoredAtom0966 Fin15AnchoredAtom0971
    Fin15AnchoredAtom1071 Fin15AnchoredAtom1576 Fin15AnchoredAtom3292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01810
  ] at hbad
  tauto

theorem fin15Anchored_clause22345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0965 Fin15AnchoredAtom3294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04882
  ] at hbad
  tauto

theorem fin15Anchored_clause22346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0968 Fin15AnchoredAtom3294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04882
  ] at hbad
  tauto

theorem fin15Anchored_clause22347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom3294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04882
  ] at hbad
  tauto

theorem fin15Anchored_clause22348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1073 Fin15AnchoredAtom3294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04882
  ] at hbad
  tauto

theorem fin15Anchored_clause22349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3294 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom3294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04882
  ] at hbad
  tauto

theorem fin15Anchored_clause22350 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3294 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0965 Fin15AnchoredAtom0968 Fin15AnchoredAtom0973
    Fin15AnchoredAtom1073 Fin15AnchoredAtom1578 Fin15AnchoredAtom3294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04882
  ] at hbad
  tauto

theorem fin15Anchored_clause22351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0965 Fin15AnchoredAtom3295 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08978
  ] at hbad
  tauto

theorem fin15Anchored_clause22352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0969 Fin15AnchoredAtom3295 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08978
  ] at hbad
  tauto

theorem fin15Anchored_clause22353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom3295 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08978
  ] at hbad
  tauto

theorem fin15Anchored_clause22354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1074 Fin15AnchoredAtom3295 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08978
  ] at hbad
  tauto

theorem fin15Anchored_clause22355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3295 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1579 Fin15AnchoredAtom3295 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08978
  ] at hbad
  tauto

theorem fin15Anchored_clause22356 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3295 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0965 Fin15AnchoredAtom0969 Fin15AnchoredAtom0974
    Fin15AnchoredAtom1074 Fin15AnchoredAtom1579 Fin15AnchoredAtom3295 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08978
  ] at hbad
  tauto

theorem fin15Anchored_clause22357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0965 Fin15AnchoredAtom3296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17170
  ] at hbad
  tauto

theorem fin15Anchored_clause22358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0975 Fin15AnchoredAtom3296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17170
  ] at hbad
  tauto

theorem fin15Anchored_clause22359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1075 Fin15AnchoredAtom3296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17170
  ] at hbad
  tauto

theorem fin15Anchored_clause22360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3296 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1580 Fin15AnchoredAtom3296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17170
  ] at hbad
  tauto

theorem fin15Anchored_clause22361 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3296 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1075 chi ∧
      Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0965 Fin15AnchoredAtom0970 Fin15AnchoredAtom0975
    Fin15AnchoredAtom1075 Fin15AnchoredAtom1580 Fin15AnchoredAtom3296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17170
  ] at hbad
  tauto

theorem fin15Anchored_clause22362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom3298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05394
  ] at hbad
  tauto

theorem fin15Anchored_clause22363 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0968 Fin15AnchoredAtom3298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05394
  ] at hbad
  tauto

theorem fin15Anchored_clause22364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom3298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05394
  ] at hbad
  tauto

theorem fin15Anchored_clause22365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1077 Fin15AnchoredAtom3298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05394
  ] at hbad
  tauto

theorem fin15Anchored_clause22366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3298 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom3298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05394
  ] at hbad
  tauto

theorem fin15Anchored_clause22367 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3298 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom0968 Fin15AnchoredAtom0977
    Fin15AnchoredAtom1077 Fin15AnchoredAtom1582 Fin15AnchoredAtom3298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05394
  ] at hbad
  tauto

theorem fin15Anchored_clause22368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom3299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09490
  ] at hbad
  tauto

theorem fin15Anchored_clause22369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0969 Fin15AnchoredAtom3299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09490
  ] at hbad
  tauto

theorem fin15Anchored_clause22370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0978 Fin15AnchoredAtom3299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09490
  ] at hbad
  tauto

theorem fin15Anchored_clause22371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1078 Fin15AnchoredAtom3299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09490
  ] at hbad
  tauto

theorem fin15Anchored_clause22372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3299 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1583 Fin15AnchoredAtom3299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09490
  ] at hbad
  tauto

theorem fin15Anchored_clause22373 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3299 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom0969 Fin15AnchoredAtom0978
    Fin15AnchoredAtom1078 Fin15AnchoredAtom1583 Fin15AnchoredAtom3299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09490
  ] at hbad
  tauto

theorem fin15Anchored_clause22374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom3300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17682
  ] at hbad
  tauto

theorem fin15Anchored_clause22375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0970 Fin15AnchoredAtom3300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17682
  ] at hbad
  tauto

theorem fin15Anchored_clause22376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0979 Fin15AnchoredAtom3300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17682
  ] at hbad
  tauto

theorem fin15Anchored_clause22377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1079 Fin15AnchoredAtom3300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17682
  ] at hbad
  tauto

theorem fin15Anchored_clause22378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3300 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1584 Fin15AnchoredAtom3300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17682
  ] at hbad
  tauto

theorem fin15Anchored_clause22379 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3300 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1079 chi ∧
      Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom0970 Fin15AnchoredAtom0979
    Fin15AnchoredAtom1079 Fin15AnchoredAtom1584 Fin15AnchoredAtom3300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17682
  ] at hbad
  tauto

theorem fin15Anchored_clause22380 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0968 Fin15AnchoredAtom3304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12562
  ] at hbad
  tauto

theorem fin15Anchored_clause22381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0969 Fin15AnchoredAtom3304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12562
  ] at hbad
  tauto

theorem fin15Anchored_clause22382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom3304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12562
  ] at hbad
  tauto

theorem fin15Anchored_clause22383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1083 Fin15AnchoredAtom3304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12562
  ] at hbad
  tauto

theorem fin15Anchored_clause22384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3304 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1588 Fin15AnchoredAtom3304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12562
  ] at hbad
  tauto

theorem fin15Anchored_clause22385 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0968 Fin15AnchoredAtom0969 Fin15AnchoredAtom0983
    Fin15AnchoredAtom1083 Fin15AnchoredAtom1588 Fin15AnchoredAtom3304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12562
  ] at hbad
  tauto

theorem fin15Anchored_clause22386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0968 Fin15AnchoredAtom3305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20754
  ] at hbad
  tauto

theorem fin15Anchored_clause22387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0984 Fin15AnchoredAtom3305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20754
  ] at hbad
  tauto

theorem fin15Anchored_clause22388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1084 Fin15AnchoredAtom3305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20754
  ] at hbad
  tauto

theorem fin15Anchored_clause22389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3305 chi ∧
      ¬Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1589 Fin15AnchoredAtom3305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20754
  ] at hbad
  tauto

theorem fin15Anchored_clause22390 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3305 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0968 Fin15AnchoredAtom0970 Fin15AnchoredAtom0984
    Fin15AnchoredAtom1084 Fin15AnchoredAtom1589 Fin15AnchoredAtom3305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20754
  ] at hbad
  tauto

theorem fin15Anchored_clause22391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0969 Fin15AnchoredAtom3306 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24850
  ] at hbad
  tauto

theorem fin15Anchored_clause22392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0970 Fin15AnchoredAtom3306 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24850
  ] at hbad
  tauto

theorem fin15Anchored_clause22393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0985 Fin15AnchoredAtom3306 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24850
  ] at hbad
  tauto

theorem fin15Anchored_clause22394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1085 Fin15AnchoredAtom3306 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24850
  ] at hbad
  tauto

theorem fin15Anchored_clause22395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3306 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1590 Fin15AnchoredAtom3306 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24850
  ] at hbad
  tauto

theorem fin15Anchored_clause22396 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3306 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0969 Fin15AnchoredAtom0970 Fin15AnchoredAtom0985
    Fin15AnchoredAtom1085 Fin15AnchoredAtom1590 Fin15AnchoredAtom3306 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24850
  ] at hbad
  tauto

theorem fin15Anchored_clause22397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3307 chi ∧
      ¬Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1591 Fin15AnchoredAtom3307 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03602
  ] at hbad
  tauto

theorem fin15Anchored_clause22398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom3308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05650
  ] at hbad
  tauto

theorem fin15Anchored_clause22399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom3308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05650
  ] at hbad
  tauto

end ErdosSzekeres

end
