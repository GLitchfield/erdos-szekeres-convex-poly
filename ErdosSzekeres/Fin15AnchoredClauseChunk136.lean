module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 136. -/

theorem fin15Anchored_clause17408 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom0558 Fin15AnchoredAtom0573
    Fin15AnchoredAtom0709 Fin15AnchoredAtom1215 Fin15AnchoredAtom2216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00677
  ] at hbad
  tauto

theorem fin15Anchored_clause17409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom2217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01189
  ] at hbad
  tauto

theorem fin15Anchored_clause17410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom2217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01189
  ] at hbad
  tauto

theorem fin15Anchored_clause17411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom2217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01189
  ] at hbad
  tauto

theorem fin15Anchored_clause17412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom2217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01189
  ] at hbad
  tauto

theorem fin15Anchored_clause17413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom2217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01189
  ] at hbad
  tauto

theorem fin15Anchored_clause17414 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom0559 Fin15AnchoredAtom0574
    Fin15AnchoredAtom0710 Fin15AnchoredAtom1216 Fin15AnchoredAtom2217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01189
  ] at hbad
  tauto

theorem fin15Anchored_clause17415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2218 chi ∧
      ¬Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom2218 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02213
  ] at hbad
  tauto

theorem fin15Anchored_clause17416 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2218 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom1217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom0560 Fin15AnchoredAtom0575
    Fin15AnchoredAtom0711 Fin15AnchoredAtom1217 Fin15AnchoredAtom2218 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02213
  ] at hbad
  tauto

theorem fin15Anchored_clause17417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom2219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04261
  ] at hbad
  tauto

theorem fin15Anchored_clause17418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom2219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04261
  ] at hbad
  tauto

theorem fin15Anchored_clause17419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom2219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04261
  ] at hbad
  tauto

theorem fin15Anchored_clause17420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom2219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04261
  ] at hbad
  tauto

theorem fin15Anchored_clause17421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom2219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04261
  ] at hbad
  tauto

theorem fin15Anchored_clause17422 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom0561 Fin15AnchoredAtom0576
    Fin15AnchoredAtom0712 Fin15AnchoredAtom1218 Fin15AnchoredAtom2219 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04261
  ] at hbad
  tauto

theorem fin15Anchored_clause17423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom2220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08357
  ] at hbad
  tauto

theorem fin15Anchored_clause17424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom2220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08357
  ] at hbad
  tauto

theorem fin15Anchored_clause17425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom2220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08357
  ] at hbad
  tauto

theorem fin15Anchored_clause17426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom2220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08357
  ] at hbad
  tauto

theorem fin15Anchored_clause17427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1219 Fin15AnchoredAtom2220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08357
  ] at hbad
  tauto

theorem fin15Anchored_clause17428 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom0562 Fin15AnchoredAtom0577
    Fin15AnchoredAtom0713 Fin15AnchoredAtom1219 Fin15AnchoredAtom2220 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08357
  ] at hbad
  tauto

theorem fin15Anchored_clause17429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom2221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16549
  ] at hbad
  tauto

theorem fin15Anchored_clause17430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0563 Fin15AnchoredAtom2221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16549
  ] at hbad
  tauto

theorem fin15Anchored_clause17431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0578 Fin15AnchoredAtom2221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16549
  ] at hbad
  tauto

theorem fin15Anchored_clause17432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0714 Fin15AnchoredAtom2221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16549
  ] at hbad
  tauto

theorem fin15Anchored_clause17433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1220 Fin15AnchoredAtom2221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16549
  ] at hbad
  tauto

theorem fin15Anchored_clause17434 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom0563 Fin15AnchoredAtom0578
    Fin15AnchoredAtom0714 Fin15AnchoredAtom1220 Fin15AnchoredAtom2221 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16549
  ] at hbad
  tauto

theorem fin15Anchored_clause17435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2222 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom2222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00805
  ] at hbad
  tauto

theorem fin15Anchored_clause17436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2222 chi ∧
      ¬Fin15AnchoredAtom0579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0579 Fin15AnchoredAtom2222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00805
  ] at hbad
  tauto

theorem fin15Anchored_clause17437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2222 chi ∧
      ¬Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom2222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00805
  ] at hbad
  tauto

theorem fin15Anchored_clause17438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2222 chi ∧
      ¬Fin15AnchoredAtom1221 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1221 Fin15AnchoredAtom2222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00805
  ] at hbad
  tauto

theorem fin15Anchored_clause17439 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2222 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom1221 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0557 Fin15AnchoredAtom0558 Fin15AnchoredAtom0579
    Fin15AnchoredAtom0715 Fin15AnchoredAtom1221 Fin15AnchoredAtom2222 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00805
  ] at hbad
  tauto

theorem fin15Anchored_clause17440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom0557 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0557 Fin15AnchoredAtom2223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01317
  ] at hbad
  tauto

theorem fin15Anchored_clause17441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom2223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01317
  ] at hbad
  tauto

theorem fin15Anchored_clause17442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom0580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0580 Fin15AnchoredAtom2223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01317
  ] at hbad
  tauto

theorem fin15Anchored_clause17443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom0716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom2223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01317
  ] at hbad
  tauto

theorem fin15Anchored_clause17444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2223 chi ∧
      ¬Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1222 Fin15AnchoredAtom2223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01317
  ] at hbad
  tauto

theorem fin15Anchored_clause17445 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2223 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0557 Fin15AnchoredAtom0559 Fin15AnchoredAtom0580
    Fin15AnchoredAtom0716 Fin15AnchoredAtom1222 Fin15AnchoredAtom2223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01317
  ] at hbad
  tauto

theorem fin15Anchored_clause17446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2225 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom2225 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04389
  ] at hbad
  tauto

theorem fin15Anchored_clause17447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2226 chi ∧
      ¬Fin15AnchoredAtom0557 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0557 Fin15AnchoredAtom2226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08485
  ] at hbad
  tauto

theorem fin15Anchored_clause17448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2226 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom2226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08485
  ] at hbad
  tauto

theorem fin15Anchored_clause17449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2226 chi ∧
      ¬Fin15AnchoredAtom0719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0719 Fin15AnchoredAtom2226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08485
  ] at hbad
  tauto

theorem fin15Anchored_clause17450 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2227 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom1226 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0557 Fin15AnchoredAtom0563 Fin15AnchoredAtom0584
    Fin15AnchoredAtom0720 Fin15AnchoredAtom1226 Fin15AnchoredAtom2227 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16677
  ] at hbad
  tauto

theorem fin15Anchored_clause17451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom2228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01573
  ] at hbad
  tauto

theorem fin15Anchored_clause17452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom2228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01573
  ] at hbad
  tauto

theorem fin15Anchored_clause17453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom2228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01573
  ] at hbad
  tauto

theorem fin15Anchored_clause17454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom2228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01573
  ] at hbad
  tauto

theorem fin15Anchored_clause17455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom2228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01573
  ] at hbad
  tauto

theorem fin15Anchored_clause17456 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom0559 Fin15AnchoredAtom0585
    Fin15AnchoredAtom0721 Fin15AnchoredAtom1227 Fin15AnchoredAtom2228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01573
  ] at hbad
  tauto

theorem fin15Anchored_clause17457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2229 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom2229 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02597
  ] at hbad
  tauto

theorem fin15Anchored_clause17458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom2230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04645
  ] at hbad
  tauto

theorem fin15Anchored_clause17459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom2230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04645
  ] at hbad
  tauto

theorem fin15Anchored_clause17460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom2230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04645
  ] at hbad
  tauto

theorem fin15Anchored_clause17461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom2230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04645
  ] at hbad
  tauto

theorem fin15Anchored_clause17462 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom2230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04645
  ] at hbad
  tauto

theorem fin15Anchored_clause17463 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom0561 Fin15AnchoredAtom0587
    Fin15AnchoredAtom0723 Fin15AnchoredAtom1229 Fin15AnchoredAtom2230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04645
  ] at hbad
  tauto

theorem fin15Anchored_clause17464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom2231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08741
  ] at hbad
  tauto

theorem fin15Anchored_clause17465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom2231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08741
  ] at hbad
  tauto

theorem fin15Anchored_clause17466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0588 Fin15AnchoredAtom2231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08741
  ] at hbad
  tauto

theorem fin15Anchored_clause17467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0724 Fin15AnchoredAtom2231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08741
  ] at hbad
  tauto

theorem fin15Anchored_clause17468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1230 Fin15AnchoredAtom2231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08741
  ] at hbad
  tauto

theorem fin15Anchored_clause17469 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom0562 Fin15AnchoredAtom0588
    Fin15AnchoredAtom0724 Fin15AnchoredAtom1230 Fin15AnchoredAtom2231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08741
  ] at hbad
  tauto

theorem fin15Anchored_clause17470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom2232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16933
  ] at hbad
  tauto

theorem fin15Anchored_clause17471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0563 Fin15AnchoredAtom2232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16933
  ] at hbad
  tauto

theorem fin15Anchored_clause17472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0589 Fin15AnchoredAtom2232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16933
  ] at hbad
  tauto

theorem fin15Anchored_clause17473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0725 Fin15AnchoredAtom2232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16933
  ] at hbad
  tauto

theorem fin15Anchored_clause17474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1231 Fin15AnchoredAtom2232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16933
  ] at hbad
  tauto

theorem fin15Anchored_clause17475 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom0563 Fin15AnchoredAtom0589
    Fin15AnchoredAtom0725 Fin15AnchoredAtom1231 Fin15AnchoredAtom2232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16933
  ] at hbad
  tauto

theorem fin15Anchored_clause17476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom2233 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03109
  ] at hbad
  tauto

theorem fin15Anchored_clause17477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom0560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0560 Fin15AnchoredAtom2233 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03109
  ] at hbad
  tauto

theorem fin15Anchored_clause17478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom0590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0590 Fin15AnchoredAtom2233 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03109
  ] at hbad
  tauto

theorem fin15Anchored_clause17479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom0726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0726 Fin15AnchoredAtom2233 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03109
  ] at hbad
  tauto

theorem fin15Anchored_clause17480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2233 chi ∧
      ¬Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1232 Fin15AnchoredAtom2233 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03109
  ] at hbad
  tauto

theorem fin15Anchored_clause17481 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2233 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom0560 Fin15AnchoredAtom0590
    Fin15AnchoredAtom0726 Fin15AnchoredAtom1232 Fin15AnchoredAtom2233 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03109
  ] at hbad
  tauto

theorem fin15Anchored_clause17482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom2234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05157
  ] at hbad
  tauto

theorem fin15Anchored_clause17483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom2234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05157
  ] at hbad
  tauto

theorem fin15Anchored_clause17484 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom2234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05157
  ] at hbad
  tauto

theorem fin15Anchored_clause17485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom2234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05157
  ] at hbad
  tauto

theorem fin15Anchored_clause17486 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1233 Fin15AnchoredAtom2234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05157
  ] at hbad
  tauto

theorem fin15Anchored_clause17487 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom0561 Fin15AnchoredAtom0591
    Fin15AnchoredAtom0727 Fin15AnchoredAtom1233 Fin15AnchoredAtom2234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05157
  ] at hbad
  tauto

theorem fin15Anchored_clause17488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom2235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09253
  ] at hbad
  tauto

theorem fin15Anchored_clause17489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom2235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09253
  ] at hbad
  tauto

theorem fin15Anchored_clause17490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0592 Fin15AnchoredAtom2235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09253
  ] at hbad
  tauto

theorem fin15Anchored_clause17491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom2235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09253
  ] at hbad
  tauto

theorem fin15Anchored_clause17492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom2235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09253
  ] at hbad
  tauto

theorem fin15Anchored_clause17493 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom0562 Fin15AnchoredAtom0592
    Fin15AnchoredAtom0728 Fin15AnchoredAtom1234 Fin15AnchoredAtom2235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09253
  ] at hbad
  tauto

theorem fin15Anchored_clause17494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom2236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17445
  ] at hbad
  tauto

theorem fin15Anchored_clause17495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0563 Fin15AnchoredAtom2236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17445
  ] at hbad
  tauto

theorem fin15Anchored_clause17496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0593 Fin15AnchoredAtom2236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17445
  ] at hbad
  tauto

theorem fin15Anchored_clause17497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0729 Fin15AnchoredAtom2236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17445
  ] at hbad
  tauto

theorem fin15Anchored_clause17498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1235 Fin15AnchoredAtom2236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17445
  ] at hbad
  tauto

theorem fin15Anchored_clause17499 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom0563 Fin15AnchoredAtom0593
    Fin15AnchoredAtom0729 Fin15AnchoredAtom1235 Fin15AnchoredAtom2236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17445
  ] at hbad
  tauto

theorem fin15Anchored_clause17500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2237 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom2237 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06181
  ] at hbad
  tauto

theorem fin15Anchored_clause17501 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2237 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom1236 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0560 Fin15AnchoredAtom0561 Fin15AnchoredAtom0594
    Fin15AnchoredAtom0730 Fin15AnchoredAtom1236 Fin15AnchoredAtom2237 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06181
  ] at hbad
  tauto

theorem fin15Anchored_clause17502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2238 chi ∧
      ¬Fin15AnchoredAtom0560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0560 Fin15AnchoredAtom2238 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10277
  ] at hbad
  tauto

theorem fin15Anchored_clause17503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2238 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom2238 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10277
  ] at hbad
  tauto

theorem fin15Anchored_clause17504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2238 chi ∧
      ¬Fin15AnchoredAtom1237 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1237 Fin15AnchoredAtom2238 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10277
  ] at hbad
  tauto

theorem fin15Anchored_clause17505 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2238 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom1237 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0560 Fin15AnchoredAtom0562 Fin15AnchoredAtom0595
    Fin15AnchoredAtom0731 Fin15AnchoredAtom1237 Fin15AnchoredAtom2238 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10277
  ] at hbad
  tauto

theorem fin15Anchored_clause17506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2239 chi ∧
      ¬Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0563 Fin15AnchoredAtom2239 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18469
  ] at hbad
  tauto

theorem fin15Anchored_clause17507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom2240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12325
  ] at hbad
  tauto

theorem fin15Anchored_clause17508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom2240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12325
  ] at hbad
  tauto

theorem fin15Anchored_clause17509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0597 Fin15AnchoredAtom2240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12325
  ] at hbad
  tauto

theorem fin15Anchored_clause17510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom2240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12325
  ] at hbad
  tauto

theorem fin15Anchored_clause17511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1239 Fin15AnchoredAtom2240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12325
  ] at hbad
  tauto

theorem fin15Anchored_clause17512 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom0562 Fin15AnchoredAtom0597
    Fin15AnchoredAtom0733 Fin15AnchoredAtom1239 Fin15AnchoredAtom2240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12325
  ] at hbad
  tauto

theorem fin15Anchored_clause17513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom2241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20517
  ] at hbad
  tauto

theorem fin15Anchored_clause17514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0563 Fin15AnchoredAtom2241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20517
  ] at hbad
  tauto

theorem fin15Anchored_clause17515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0598 Fin15AnchoredAtom2241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20517
  ] at hbad
  tauto

theorem fin15Anchored_clause17516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0734 Fin15AnchoredAtom2241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20517
  ] at hbad
  tauto

theorem fin15Anchored_clause17517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1240 Fin15AnchoredAtom2241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20517
  ] at hbad
  tauto

theorem fin15Anchored_clause17518 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom0563 Fin15AnchoredAtom0598
    Fin15AnchoredAtom0734 Fin15AnchoredAtom1240 Fin15AnchoredAtom2241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20517
  ] at hbad
  tauto

theorem fin15Anchored_clause17519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom2242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24613
  ] at hbad
  tauto

theorem fin15Anchored_clause17520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0563 Fin15AnchoredAtom2242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24613
  ] at hbad
  tauto

theorem fin15Anchored_clause17521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0599 Fin15AnchoredAtom2242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24613
  ] at hbad
  tauto

theorem fin15Anchored_clause17522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0735 Fin15AnchoredAtom2242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24613
  ] at hbad
  tauto

theorem fin15Anchored_clause17523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1241 Fin15AnchoredAtom2242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24613
  ] at hbad
  tauto

theorem fin15Anchored_clause17524 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom0563 Fin15AnchoredAtom0599
    Fin15AnchoredAtom0735 Fin15AnchoredAtom1241 Fin15AnchoredAtom2242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24613
  ] at hbad
  tauto

theorem fin15Anchored_clause17525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2243 chi ∧
      ¬Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom2243 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00453
  ] at hbad
  tauto

theorem fin15Anchored_clause17526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2243 chi ∧
      ¬Fin15AnchoredAtom1242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1242 Fin15AnchoredAtom2243 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00453
  ] at hbad
  tauto

theorem fin15Anchored_clause17527 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2243 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom1242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom0565 Fin15AnchoredAtom0572
    Fin15AnchoredAtom0736 Fin15AnchoredAtom1242 Fin15AnchoredAtom2243 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00453
  ] at hbad
  tauto

theorem fin15Anchored_clause17528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom2244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00709
  ] at hbad
  tauto

theorem fin15Anchored_clause17529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom2244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00709
  ] at hbad
  tauto

theorem fin15Anchored_clause17530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom2244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00709
  ] at hbad
  tauto

theorem fin15Anchored_clause17531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom2244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00709
  ] at hbad
  tauto

theorem fin15Anchored_clause17532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom2244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00709
  ] at hbad
  tauto

theorem fin15Anchored_clause17533 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom0566 Fin15AnchoredAtom0573
    Fin15AnchoredAtom0737 Fin15AnchoredAtom1243 Fin15AnchoredAtom2244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00709
  ] at hbad
  tauto

theorem fin15Anchored_clause17534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom2245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01221
  ] at hbad
  tauto

theorem fin15Anchored_clause17535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom2245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01221
  ] at hbad
  tauto

end ErdosSzekeres

end
