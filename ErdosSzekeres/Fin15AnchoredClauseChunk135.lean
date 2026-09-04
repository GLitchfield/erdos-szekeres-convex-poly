module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 135. -/

theorem fin15Anchored_clause17280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2191 chi ∧
      ¬Fin15AnchoredAtom0584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0584 Fin15AnchoredAtom2191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16661
  ] at hbad
  tauto

theorem fin15Anchored_clause17281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2191 chi ∧
      ¬Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0684 Fin15AnchoredAtom2191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16661
  ] at hbad
  tauto

theorem fin15Anchored_clause17282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2191 chi ∧
      ¬Fin15AnchoredAtom1190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1190 Fin15AnchoredAtom2191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16661
  ] at hbad
  tauto

theorem fin15Anchored_clause17283 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2191 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom1190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0548 Fin15AnchoredAtom0554 Fin15AnchoredAtom0584
    Fin15AnchoredAtom0684 Fin15AnchoredAtom1190 Fin15AnchoredAtom2191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16661
  ] at hbad
  tauto

theorem fin15Anchored_clause17284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom2192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01557
  ] at hbad
  tauto

theorem fin15Anchored_clause17285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom2192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01557
  ] at hbad
  tauto

theorem fin15Anchored_clause17286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom2192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01557
  ] at hbad
  tauto

theorem fin15Anchored_clause17287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom2192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01557
  ] at hbad
  tauto

theorem fin15Anchored_clause17288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom2192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01557
  ] at hbad
  tauto

theorem fin15Anchored_clause17289 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom0550 Fin15AnchoredAtom0585
    Fin15AnchoredAtom0685 Fin15AnchoredAtom1191 Fin15AnchoredAtom2192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01557
  ] at hbad
  tauto

theorem fin15Anchored_clause17290 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2193 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom2193 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02581
  ] at hbad
  tauto

theorem fin15Anchored_clause17291 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2193 chi ∧
      ¬Fin15AnchoredAtom0551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0551 Fin15AnchoredAtom2193 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02581
  ] at hbad
  tauto

theorem fin15Anchored_clause17292 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2193 chi ∧
      ¬Fin15AnchoredAtom0686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0686 Fin15AnchoredAtom2193 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02581
  ] at hbad
  tauto

theorem fin15Anchored_clause17293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom2194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04629
  ] at hbad
  tauto

theorem fin15Anchored_clause17294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom2194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04629
  ] at hbad
  tauto

theorem fin15Anchored_clause17295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom2194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04629
  ] at hbad
  tauto

theorem fin15Anchored_clause17296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom2194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04629
  ] at hbad
  tauto

theorem fin15Anchored_clause17297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom2194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04629
  ] at hbad
  tauto

theorem fin15Anchored_clause17298 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom0552 Fin15AnchoredAtom0587
    Fin15AnchoredAtom0687 Fin15AnchoredAtom1193 Fin15AnchoredAtom2194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04629
  ] at hbad
  tauto

theorem fin15Anchored_clause17299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom2195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08725
  ] at hbad
  tauto

theorem fin15Anchored_clause17300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0553 Fin15AnchoredAtom2195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08725
  ] at hbad
  tauto

theorem fin15Anchored_clause17301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0588 Fin15AnchoredAtom2195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08725
  ] at hbad
  tauto

theorem fin15Anchored_clause17302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0688 Fin15AnchoredAtom2195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08725
  ] at hbad
  tauto

theorem fin15Anchored_clause17303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1194 Fin15AnchoredAtom2195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08725
  ] at hbad
  tauto

theorem fin15Anchored_clause17304 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom0553 Fin15AnchoredAtom0588
    Fin15AnchoredAtom0688 Fin15AnchoredAtom1194 Fin15AnchoredAtom2195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08725
  ] at hbad
  tauto

theorem fin15Anchored_clause17305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom2196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16917
  ] at hbad
  tauto

theorem fin15Anchored_clause17306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0554 Fin15AnchoredAtom2196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16917
  ] at hbad
  tauto

theorem fin15Anchored_clause17307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0589 Fin15AnchoredAtom2196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16917
  ] at hbad
  tauto

theorem fin15Anchored_clause17308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0689 Fin15AnchoredAtom2196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16917
  ] at hbad
  tauto

theorem fin15Anchored_clause17309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1195 Fin15AnchoredAtom2196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16917
  ] at hbad
  tauto

theorem fin15Anchored_clause17310 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom0554 Fin15AnchoredAtom0589
    Fin15AnchoredAtom0689 Fin15AnchoredAtom1195 Fin15AnchoredAtom2196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16917
  ] at hbad
  tauto

theorem fin15Anchored_clause17311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2197 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom2197 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03093
  ] at hbad
  tauto

theorem fin15Anchored_clause17312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom2198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05141
  ] at hbad
  tauto

theorem fin15Anchored_clause17313 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom2198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05141
  ] at hbad
  tauto

theorem fin15Anchored_clause17314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom2198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05141
  ] at hbad
  tauto

theorem fin15Anchored_clause17315 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom2198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05141
  ] at hbad
  tauto

theorem fin15Anchored_clause17316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom2198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05141
  ] at hbad
  tauto

theorem fin15Anchored_clause17317 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom0552 Fin15AnchoredAtom0591
    Fin15AnchoredAtom0691 Fin15AnchoredAtom1197 Fin15AnchoredAtom2198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05141
  ] at hbad
  tauto

theorem fin15Anchored_clause17318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom2199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09237
  ] at hbad
  tauto

theorem fin15Anchored_clause17319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0553 Fin15AnchoredAtom2199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09237
  ] at hbad
  tauto

theorem fin15Anchored_clause17320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0592 Fin15AnchoredAtom2199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09237
  ] at hbad
  tauto

theorem fin15Anchored_clause17321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom2199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09237
  ] at hbad
  tauto

theorem fin15Anchored_clause17322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom2199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09237
  ] at hbad
  tauto

theorem fin15Anchored_clause17323 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom0553 Fin15AnchoredAtom0592
    Fin15AnchoredAtom0692 Fin15AnchoredAtom1198 Fin15AnchoredAtom2199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09237
  ] at hbad
  tauto

theorem fin15Anchored_clause17324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom2200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17429
  ] at hbad
  tauto

theorem fin15Anchored_clause17325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0554 Fin15AnchoredAtom2200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17429
  ] at hbad
  tauto

theorem fin15Anchored_clause17326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0593 Fin15AnchoredAtom2200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17429
  ] at hbad
  tauto

theorem fin15Anchored_clause17327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0693 Fin15AnchoredAtom2200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17429
  ] at hbad
  tauto

theorem fin15Anchored_clause17328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1199 Fin15AnchoredAtom2200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17429
  ] at hbad
  tauto

theorem fin15Anchored_clause17329 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom0554 Fin15AnchoredAtom0593
    Fin15AnchoredAtom0693 Fin15AnchoredAtom1199 Fin15AnchoredAtom2200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17429
  ] at hbad
  tauto

theorem fin15Anchored_clause17330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom0551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0551 Fin15AnchoredAtom2201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06165
  ] at hbad
  tauto

theorem fin15Anchored_clause17331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom2201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06165
  ] at hbad
  tauto

theorem fin15Anchored_clause17332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom0694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0694 Fin15AnchoredAtom2201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06165
  ] at hbad
  tauto

theorem fin15Anchored_clause17333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2201 chi ∧
      ¬Fin15AnchoredAtom1200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1200 Fin15AnchoredAtom2201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06165
  ] at hbad
  tauto

theorem fin15Anchored_clause17334 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2201 chi ∧
      Fin15AnchoredAtom0551 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom1200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0551 Fin15AnchoredAtom0552 Fin15AnchoredAtom0594
    Fin15AnchoredAtom0694 Fin15AnchoredAtom1200 Fin15AnchoredAtom2201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06165
  ] at hbad
  tauto

theorem fin15Anchored_clause17335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2202 chi ∧
      ¬Fin15AnchoredAtom0551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0551 Fin15AnchoredAtom2202 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10261
  ] at hbad
  tauto

theorem fin15Anchored_clause17336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2202 chi ∧
      ¬Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0553 Fin15AnchoredAtom2202 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10261
  ] at hbad
  tauto

theorem fin15Anchored_clause17337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2203 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0554 Fin15AnchoredAtom2203 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18453
  ] at hbad
  tauto

theorem fin15Anchored_clause17338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom2204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12309
  ] at hbad
  tauto

theorem fin15Anchored_clause17339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0553 Fin15AnchoredAtom2204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12309
  ] at hbad
  tauto

theorem fin15Anchored_clause17340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0597 Fin15AnchoredAtom2204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12309
  ] at hbad
  tauto

theorem fin15Anchored_clause17341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom2204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12309
  ] at hbad
  tauto

theorem fin15Anchored_clause17342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1203 Fin15AnchoredAtom2204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12309
  ] at hbad
  tauto

theorem fin15Anchored_clause17343 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom0553 Fin15AnchoredAtom0597
    Fin15AnchoredAtom0697 Fin15AnchoredAtom1203 Fin15AnchoredAtom2204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12309
  ] at hbad
  tauto

theorem fin15Anchored_clause17344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom2205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20501
  ] at hbad
  tauto

theorem fin15Anchored_clause17345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0554 Fin15AnchoredAtom2205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20501
  ] at hbad
  tauto

theorem fin15Anchored_clause17346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0598 Fin15AnchoredAtom2205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20501
  ] at hbad
  tauto

theorem fin15Anchored_clause17347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0698 Fin15AnchoredAtom2205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20501
  ] at hbad
  tauto

theorem fin15Anchored_clause17348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1204 Fin15AnchoredAtom2205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20501
  ] at hbad
  tauto

theorem fin15Anchored_clause17349 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom0554 Fin15AnchoredAtom0598
    Fin15AnchoredAtom0698 Fin15AnchoredAtom1204 Fin15AnchoredAtom2205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20501
  ] at hbad
  tauto

theorem fin15Anchored_clause17350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0553 Fin15AnchoredAtom2206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24597
  ] at hbad
  tauto

theorem fin15Anchored_clause17351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0554 Fin15AnchoredAtom2206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24597
  ] at hbad
  tauto

theorem fin15Anchored_clause17352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0599 Fin15AnchoredAtom2206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24597
  ] at hbad
  tauto

theorem fin15Anchored_clause17353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0699 Fin15AnchoredAtom2206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24597
  ] at hbad
  tauto

theorem fin15Anchored_clause17354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1205 Fin15AnchoredAtom2206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24597
  ] at hbad
  tauto

theorem fin15Anchored_clause17355 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0553 Fin15AnchoredAtom0554 Fin15AnchoredAtom0599
    Fin15AnchoredAtom0699 Fin15AnchoredAtom1205 Fin15AnchoredAtom2206 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24597
  ] at hbad
  tauto

theorem fin15Anchored_clause17356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom2207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00229
  ] at hbad
  tauto

theorem fin15Anchored_clause17357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom2207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00229
  ] at hbad
  tauto

theorem fin15Anchored_clause17358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom2207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00229
  ] at hbad
  tauto

theorem fin15Anchored_clause17359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom2207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00229
  ] at hbad
  tauto

theorem fin15Anchored_clause17360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom2207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00229
  ] at hbad
  tauto

theorem fin15Anchored_clause17361 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom0556 Fin15AnchoredAtom0564
    Fin15AnchoredAtom0700 Fin15AnchoredAtom1206 Fin15AnchoredAtom2207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00229
  ] at hbad
  tauto

theorem fin15Anchored_clause17362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2208 chi ∧
      ¬Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom2208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00357
  ] at hbad
  tauto

theorem fin15Anchored_clause17363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2208 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom1207 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom0557 Fin15AnchoredAtom0565
    Fin15AnchoredAtom0701 Fin15AnchoredAtom1207 Fin15AnchoredAtom2208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00357
  ] at hbad
  tauto

theorem fin15Anchored_clause17364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom2209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00613
  ] at hbad
  tauto

theorem fin15Anchored_clause17365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom2209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00613
  ] at hbad
  tauto

theorem fin15Anchored_clause17366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom2209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00613
  ] at hbad
  tauto

theorem fin15Anchored_clause17367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom2209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00613
  ] at hbad
  tauto

theorem fin15Anchored_clause17368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom2209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00613
  ] at hbad
  tauto

theorem fin15Anchored_clause17369 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom0558 Fin15AnchoredAtom0566
    Fin15AnchoredAtom0702 Fin15AnchoredAtom1208 Fin15AnchoredAtom2209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00613
  ] at hbad
  tauto

theorem fin15Anchored_clause17370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom2210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01125
  ] at hbad
  tauto

theorem fin15Anchored_clause17371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom2210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01125
  ] at hbad
  tauto

theorem fin15Anchored_clause17372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom2210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01125
  ] at hbad
  tauto

theorem fin15Anchored_clause17373 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom2210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01125
  ] at hbad
  tauto

theorem fin15Anchored_clause17374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom2210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01125
  ] at hbad
  tauto

theorem fin15Anchored_clause17375 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom0559 Fin15AnchoredAtom0567
    Fin15AnchoredAtom0703 Fin15AnchoredAtom1209 Fin15AnchoredAtom2210 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01125
  ] at hbad
  tauto

theorem fin15Anchored_clause17376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2211 chi ∧
      ¬Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom2211 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02149
  ] at hbad
  tauto

theorem fin15Anchored_clause17377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2211 chi ∧
      ¬Fin15AnchoredAtom0560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0560 Fin15AnchoredAtom2211 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02149
  ] at hbad
  tauto

theorem fin15Anchored_clause17378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2211 chi ∧
      ¬Fin15AnchoredAtom0704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0704 Fin15AnchoredAtom2211 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02149
  ] at hbad
  tauto

theorem fin15Anchored_clause17379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2211 chi ∧
      ¬Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1210 Fin15AnchoredAtom2211 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02149
  ] at hbad
  tauto

theorem fin15Anchored_clause17380 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2211 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom0560 Fin15AnchoredAtom0568
    Fin15AnchoredAtom0704 Fin15AnchoredAtom1210 Fin15AnchoredAtom2211 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02149
  ] at hbad
  tauto

theorem fin15Anchored_clause17381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom2212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04197
  ] at hbad
  tauto

theorem fin15Anchored_clause17382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom2212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04197
  ] at hbad
  tauto

theorem fin15Anchored_clause17383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom2212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04197
  ] at hbad
  tauto

theorem fin15Anchored_clause17384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom2212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04197
  ] at hbad
  tauto

theorem fin15Anchored_clause17385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom2212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04197
  ] at hbad
  tauto

theorem fin15Anchored_clause17386 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom0561 Fin15AnchoredAtom0569
    Fin15AnchoredAtom0705 Fin15AnchoredAtom1211 Fin15AnchoredAtom2212 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04197
  ] at hbad
  tauto

theorem fin15Anchored_clause17387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom2213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08293
  ] at hbad
  tauto

theorem fin15Anchored_clause17388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom2213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08293
  ] at hbad
  tauto

theorem fin15Anchored_clause17389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom2213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08293
  ] at hbad
  tauto

theorem fin15Anchored_clause17390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0706 Fin15AnchoredAtom2213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08293
  ] at hbad
  tauto

theorem fin15Anchored_clause17391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1212 Fin15AnchoredAtom2213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08293
  ] at hbad
  tauto

theorem fin15Anchored_clause17392 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom0562 Fin15AnchoredAtom0570
    Fin15AnchoredAtom0706 Fin15AnchoredAtom1212 Fin15AnchoredAtom2213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08293
  ] at hbad
  tauto

theorem fin15Anchored_clause17393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom2214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16485
  ] at hbad
  tauto

theorem fin15Anchored_clause17394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0563 Fin15AnchoredAtom2214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16485
  ] at hbad
  tauto

theorem fin15Anchored_clause17395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0571 Fin15AnchoredAtom2214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16485
  ] at hbad
  tauto

theorem fin15Anchored_clause17396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0707 Fin15AnchoredAtom2214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16485
  ] at hbad
  tauto

theorem fin15Anchored_clause17397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1213 Fin15AnchoredAtom2214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16485
  ] at hbad
  tauto

theorem fin15Anchored_clause17398 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom0563 Fin15AnchoredAtom0571
    Fin15AnchoredAtom0707 Fin15AnchoredAtom1213 Fin15AnchoredAtom2214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16485
  ] at hbad
  tauto

theorem fin15Anchored_clause17399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2215 chi ∧
      ¬Fin15AnchoredAtom0572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0572 Fin15AnchoredAtom2215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00421
  ] at hbad
  tauto

theorem fin15Anchored_clause17400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2215 chi ∧
      ¬Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom2215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00421
  ] at hbad
  tauto

theorem fin15Anchored_clause17401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2215 chi ∧
      ¬Fin15AnchoredAtom1214 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1214 Fin15AnchoredAtom2215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00421
  ] at hbad
  tauto

theorem fin15Anchored_clause17402 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2215 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom1214 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom0557 Fin15AnchoredAtom0572
    Fin15AnchoredAtom0708 Fin15AnchoredAtom1214 Fin15AnchoredAtom2215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00421
  ] at hbad
  tauto

theorem fin15Anchored_clause17403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom2216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00677
  ] at hbad
  tauto

theorem fin15Anchored_clause17404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom2216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00677
  ] at hbad
  tauto

theorem fin15Anchored_clause17405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom2216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00677
  ] at hbad
  tauto

theorem fin15Anchored_clause17406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom2216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00677
  ] at hbad
  tauto

theorem fin15Anchored_clause17407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom2216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00677
  ] at hbad
  tauto

end ErdosSzekeres

end
