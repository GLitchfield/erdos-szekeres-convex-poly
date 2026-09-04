module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 142. -/

theorem fin15Anchored_clause18176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0714 Fin15AnchoredAtom2386 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16553
  ] at hbad
  tauto

theorem fin15Anchored_clause18177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1385 Fin15AnchoredAtom2386 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16553
  ] at hbad
  tauto

theorem fin15Anchored_clause18178 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom0618 Fin15AnchoredAtom0633
    Fin15AnchoredAtom0714 Fin15AnchoredAtom1385 Fin15AnchoredAtom2386 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16553
  ] at hbad
  tauto

theorem fin15Anchored_clause18179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom2387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00809
  ] at hbad
  tauto

theorem fin15Anchored_clause18180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom2387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00809
  ] at hbad
  tauto

theorem fin15Anchored_clause18181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom0634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom2387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00809
  ] at hbad
  tauto

theorem fin15Anchored_clause18182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom2387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00809
  ] at hbad
  tauto

theorem fin15Anchored_clause18183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2387 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom2387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00809
  ] at hbad
  tauto

theorem fin15Anchored_clause18184 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom0613 Fin15AnchoredAtom0634
    Fin15AnchoredAtom0715 Fin15AnchoredAtom1386 Fin15AnchoredAtom2387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00809
  ] at hbad
  tauto

theorem fin15Anchored_clause18185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom2388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01321
  ] at hbad
  tauto

theorem fin15Anchored_clause18186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom2388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01321
  ] at hbad
  tauto

theorem fin15Anchored_clause18187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom2388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01321
  ] at hbad
  tauto

theorem fin15Anchored_clause18188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom0716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom2388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01321
  ] at hbad
  tauto

theorem fin15Anchored_clause18189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2388 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom2388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01321
  ] at hbad
  tauto

theorem fin15Anchored_clause18190 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom0614 Fin15AnchoredAtom0635
    Fin15AnchoredAtom0716 Fin15AnchoredAtom1387 Fin15AnchoredAtom2388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01321
  ] at hbad
  tauto

theorem fin15Anchored_clause18191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom2390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04393
  ] at hbad
  tauto

theorem fin15Anchored_clause18192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom2390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04393
  ] at hbad
  tauto

theorem fin15Anchored_clause18193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom2390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04393
  ] at hbad
  tauto

theorem fin15Anchored_clause18194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom0718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0718 Fin15AnchoredAtom2390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04393
  ] at hbad
  tauto

theorem fin15Anchored_clause18195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2390 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1389 Fin15AnchoredAtom2390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04393
  ] at hbad
  tauto

theorem fin15Anchored_clause18196 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom0616 Fin15AnchoredAtom0637
    Fin15AnchoredAtom0718 Fin15AnchoredAtom1389 Fin15AnchoredAtom2390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04393
  ] at hbad
  tauto

theorem fin15Anchored_clause18197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom2391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08489
  ] at hbad
  tauto

theorem fin15Anchored_clause18198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom2391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08489
  ] at hbad
  tauto

theorem fin15Anchored_clause18199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom0638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0638 Fin15AnchoredAtom2391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08489
  ] at hbad
  tauto

theorem fin15Anchored_clause18200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom0719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0719 Fin15AnchoredAtom2391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08489
  ] at hbad
  tauto

theorem fin15Anchored_clause18201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2391 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1390 Fin15AnchoredAtom2391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08489
  ] at hbad
  tauto

theorem fin15Anchored_clause18202 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2391 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom0617 Fin15AnchoredAtom0638
    Fin15AnchoredAtom0719 Fin15AnchoredAtom1390 Fin15AnchoredAtom2391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08489
  ] at hbad
  tauto

theorem fin15Anchored_clause18203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom2392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16681
  ] at hbad
  tauto

theorem fin15Anchored_clause18204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0618 Fin15AnchoredAtom2392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16681
  ] at hbad
  tauto

theorem fin15Anchored_clause18205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom0639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0639 Fin15AnchoredAtom2392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16681
  ] at hbad
  tauto

theorem fin15Anchored_clause18206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom0720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0720 Fin15AnchoredAtom2392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16681
  ] at hbad
  tauto

theorem fin15Anchored_clause18207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2392 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1391 Fin15AnchoredAtom2392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16681
  ] at hbad
  tauto

theorem fin15Anchored_clause18208 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom0618 Fin15AnchoredAtom0639
    Fin15AnchoredAtom0720 Fin15AnchoredAtom1391 Fin15AnchoredAtom2392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16681
  ] at hbad
  tauto

theorem fin15Anchored_clause18209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom2393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01577
  ] at hbad
  tauto

theorem fin15Anchored_clause18210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom2393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01577
  ] at hbad
  tauto

theorem fin15Anchored_clause18211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom2393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01577
  ] at hbad
  tauto

theorem fin15Anchored_clause18212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom2393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01577
  ] at hbad
  tauto

theorem fin15Anchored_clause18213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom2393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01577
  ] at hbad
  tauto

theorem fin15Anchored_clause18214 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom0614 Fin15AnchoredAtom0640
    Fin15AnchoredAtom0721 Fin15AnchoredAtom1392 Fin15AnchoredAtom2393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01577
  ] at hbad
  tauto

theorem fin15Anchored_clause18215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2394 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom2394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02601
  ] at hbad
  tauto

theorem fin15Anchored_clause18216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2394 chi ∧
      ¬Fin15AnchoredAtom0722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0722 Fin15AnchoredAtom2394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02601
  ] at hbad
  tauto

theorem fin15Anchored_clause18217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2394 chi ∧
      ¬Fin15AnchoredAtom1393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1393 Fin15AnchoredAtom2394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02601
  ] at hbad
  tauto

theorem fin15Anchored_clause18218 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2394 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom1393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom0615 Fin15AnchoredAtom0641
    Fin15AnchoredAtom0722 Fin15AnchoredAtom1393 Fin15AnchoredAtom2394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02601
  ] at hbad
  tauto

theorem fin15Anchored_clause18219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom2395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04649
  ] at hbad
  tauto

theorem fin15Anchored_clause18220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom2395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04649
  ] at hbad
  tauto

theorem fin15Anchored_clause18221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom2395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04649
  ] at hbad
  tauto

theorem fin15Anchored_clause18222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom2395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04649
  ] at hbad
  tauto

theorem fin15Anchored_clause18223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom2395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04649
  ] at hbad
  tauto

theorem fin15Anchored_clause18224 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom0616 Fin15AnchoredAtom0642
    Fin15AnchoredAtom0723 Fin15AnchoredAtom1394 Fin15AnchoredAtom2395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04649
  ] at hbad
  tauto

theorem fin15Anchored_clause18225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom2396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08745
  ] at hbad
  tauto

theorem fin15Anchored_clause18226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom2396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08745
  ] at hbad
  tauto

theorem fin15Anchored_clause18227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0643 Fin15AnchoredAtom2396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08745
  ] at hbad
  tauto

theorem fin15Anchored_clause18228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0724 Fin15AnchoredAtom2396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08745
  ] at hbad
  tauto

theorem fin15Anchored_clause18229 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1395 Fin15AnchoredAtom2396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08745
  ] at hbad
  tauto

theorem fin15Anchored_clause18230 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom0617 Fin15AnchoredAtom0643
    Fin15AnchoredAtom0724 Fin15AnchoredAtom1395 Fin15AnchoredAtom2396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08745
  ] at hbad
  tauto

theorem fin15Anchored_clause18231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom2397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16937
  ] at hbad
  tauto

theorem fin15Anchored_clause18232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0618 Fin15AnchoredAtom2397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16937
  ] at hbad
  tauto

theorem fin15Anchored_clause18233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0644 Fin15AnchoredAtom2397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16937
  ] at hbad
  tauto

theorem fin15Anchored_clause18234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0725 Fin15AnchoredAtom2397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16937
  ] at hbad
  tauto

theorem fin15Anchored_clause18235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1396 Fin15AnchoredAtom2397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16937
  ] at hbad
  tauto

theorem fin15Anchored_clause18236 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom0618 Fin15AnchoredAtom0644
    Fin15AnchoredAtom0725 Fin15AnchoredAtom1396 Fin15AnchoredAtom2397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16937
  ] at hbad
  tauto

theorem fin15Anchored_clause18237 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom2398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03113
  ] at hbad
  tauto

theorem fin15Anchored_clause18238 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom0615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0615 Fin15AnchoredAtom2398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03113
  ] at hbad
  tauto

theorem fin15Anchored_clause18239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom0645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0645 Fin15AnchoredAtom2398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03113
  ] at hbad
  tauto

theorem fin15Anchored_clause18240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom0726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0726 Fin15AnchoredAtom2398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03113
  ] at hbad
  tauto

theorem fin15Anchored_clause18241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2398 chi ∧
      ¬Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1397 Fin15AnchoredAtom2398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03113
  ] at hbad
  tauto

theorem fin15Anchored_clause18242 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2398 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom0615 Fin15AnchoredAtom0645
    Fin15AnchoredAtom0726 Fin15AnchoredAtom1397 Fin15AnchoredAtom2398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03113
  ] at hbad
  tauto

theorem fin15Anchored_clause18243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom2399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05161
  ] at hbad
  tauto

theorem fin15Anchored_clause18244 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom2399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05161
  ] at hbad
  tauto

theorem fin15Anchored_clause18245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom2399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05161
  ] at hbad
  tauto

theorem fin15Anchored_clause18246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom2399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05161
  ] at hbad
  tauto

theorem fin15Anchored_clause18247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom2399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05161
  ] at hbad
  tauto

theorem fin15Anchored_clause18248 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom0616 Fin15AnchoredAtom0646
    Fin15AnchoredAtom0727 Fin15AnchoredAtom1398 Fin15AnchoredAtom2399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05161
  ] at hbad
  tauto

theorem fin15Anchored_clause18249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom2400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09257
  ] at hbad
  tauto

theorem fin15Anchored_clause18250 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom2400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09257
  ] at hbad
  tauto

theorem fin15Anchored_clause18251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom2400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09257
  ] at hbad
  tauto

theorem fin15Anchored_clause18252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom2400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09257
  ] at hbad
  tauto

theorem fin15Anchored_clause18253 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom2400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09257
  ] at hbad
  tauto

theorem fin15Anchored_clause18254 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom0617 Fin15AnchoredAtom0647
    Fin15AnchoredAtom0728 Fin15AnchoredAtom1399 Fin15AnchoredAtom2400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09257
  ] at hbad
  tauto

theorem fin15Anchored_clause18255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom2401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17449
  ] at hbad
  tauto

theorem fin15Anchored_clause18256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0618 Fin15AnchoredAtom2401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17449
  ] at hbad
  tauto

theorem fin15Anchored_clause18257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0648 Fin15AnchoredAtom2401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17449
  ] at hbad
  tauto

theorem fin15Anchored_clause18258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0729 Fin15AnchoredAtom2401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17449
  ] at hbad
  tauto

theorem fin15Anchored_clause18259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1400 Fin15AnchoredAtom2401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17449
  ] at hbad
  tauto

theorem fin15Anchored_clause18260 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom0618 Fin15AnchoredAtom0648
    Fin15AnchoredAtom0729 Fin15AnchoredAtom1400 Fin15AnchoredAtom2401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17449
  ] at hbad
  tauto

theorem fin15Anchored_clause18261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2402 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom2402 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06185
  ] at hbad
  tauto

theorem fin15Anchored_clause18262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2402 chi ∧
      ¬Fin15AnchoredAtom0649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0649 Fin15AnchoredAtom2402 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06185
  ] at hbad
  tauto

theorem fin15Anchored_clause18263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2402 chi ∧
      ¬Fin15AnchoredAtom0730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0730 Fin15AnchoredAtom2402 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06185
  ] at hbad
  tauto

theorem fin15Anchored_clause18264 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2402 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom1401 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0615 Fin15AnchoredAtom0616 Fin15AnchoredAtom0649
    Fin15AnchoredAtom0730 Fin15AnchoredAtom1401 Fin15AnchoredAtom2402 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06185
  ] at hbad
  tauto

theorem fin15Anchored_clause18265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom0615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0615 Fin15AnchoredAtom2403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10281
  ] at hbad
  tauto

theorem fin15Anchored_clause18266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom2403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10281
  ] at hbad
  tauto

theorem fin15Anchored_clause18267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom0650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0650 Fin15AnchoredAtom2403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10281
  ] at hbad
  tauto

theorem fin15Anchored_clause18268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom0731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0731 Fin15AnchoredAtom2403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10281
  ] at hbad
  tauto

theorem fin15Anchored_clause18269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2403 chi ∧
      ¬Fin15AnchoredAtom1402 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1402 Fin15AnchoredAtom2403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10281
  ] at hbad
  tauto

theorem fin15Anchored_clause18270 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2403 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom1402 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0615 Fin15AnchoredAtom0617 Fin15AnchoredAtom0650
    Fin15AnchoredAtom0731 Fin15AnchoredAtom1402 Fin15AnchoredAtom2403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10281
  ] at hbad
  tauto

theorem fin15Anchored_clause18271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2404 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0618 Fin15AnchoredAtom2404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18473
  ] at hbad
  tauto

theorem fin15Anchored_clause18272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2404 chi ∧
      ¬Fin15AnchoredAtom1403 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1403 Fin15AnchoredAtom2404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18473
  ] at hbad
  tauto

theorem fin15Anchored_clause18273 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2404 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0651 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom1403 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0615 Fin15AnchoredAtom0618 Fin15AnchoredAtom0651
    Fin15AnchoredAtom0732 Fin15AnchoredAtom1403 Fin15AnchoredAtom2404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18473
  ] at hbad
  tauto

theorem fin15Anchored_clause18274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom2405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12329
  ] at hbad
  tauto

theorem fin15Anchored_clause18275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom2405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12329
  ] at hbad
  tauto

theorem fin15Anchored_clause18276 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom2405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12329
  ] at hbad
  tauto

theorem fin15Anchored_clause18277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom2405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12329
  ] at hbad
  tauto

theorem fin15Anchored_clause18278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1404 Fin15AnchoredAtom2405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12329
  ] at hbad
  tauto

theorem fin15Anchored_clause18279 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom0617 Fin15AnchoredAtom0652
    Fin15AnchoredAtom0733 Fin15AnchoredAtom1404 Fin15AnchoredAtom2405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12329
  ] at hbad
  tauto

theorem fin15Anchored_clause18280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom2406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20521
  ] at hbad
  tauto

theorem fin15Anchored_clause18281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0618 Fin15AnchoredAtom2406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20521
  ] at hbad
  tauto

theorem fin15Anchored_clause18282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0653 Fin15AnchoredAtom2406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20521
  ] at hbad
  tauto

theorem fin15Anchored_clause18283 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0734 Fin15AnchoredAtom2406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20521
  ] at hbad
  tauto

theorem fin15Anchored_clause18284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1405 Fin15AnchoredAtom2406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20521
  ] at hbad
  tauto

theorem fin15Anchored_clause18285 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom0618 Fin15AnchoredAtom0653
    Fin15AnchoredAtom0734 Fin15AnchoredAtom1405 Fin15AnchoredAtom2406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20521
  ] at hbad
  tauto

theorem fin15Anchored_clause18286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom2407 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24617
  ] at hbad
  tauto

theorem fin15Anchored_clause18287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0618 Fin15AnchoredAtom2407 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24617
  ] at hbad
  tauto

theorem fin15Anchored_clause18288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0654 Fin15AnchoredAtom2407 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24617
  ] at hbad
  tauto

theorem fin15Anchored_clause18289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0735 Fin15AnchoredAtom2407 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24617
  ] at hbad
  tauto

theorem fin15Anchored_clause18290 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1406 Fin15AnchoredAtom2407 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24617
  ] at hbad
  tauto

theorem fin15Anchored_clause18291 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom0618 Fin15AnchoredAtom0654
    Fin15AnchoredAtom0735 Fin15AnchoredAtom1406 Fin15AnchoredAtom2407 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24617
  ] at hbad
  tauto

theorem fin15Anchored_clause18292 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom2408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00457
  ] at hbad
  tauto

theorem fin15Anchored_clause18293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom2408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00457
  ] at hbad
  tauto

theorem fin15Anchored_clause18294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom2408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00457
  ] at hbad
  tauto

theorem fin15Anchored_clause18295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom0736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom2408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00457
  ] at hbad
  tauto

theorem fin15Anchored_clause18296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2408 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom2408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00457
  ] at hbad
  tauto

theorem fin15Anchored_clause18297 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom0620 Fin15AnchoredAtom0627
    Fin15AnchoredAtom0736 Fin15AnchoredAtom1407 Fin15AnchoredAtom2408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00457
  ] at hbad
  tauto

theorem fin15Anchored_clause18298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom2409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00713
  ] at hbad
  tauto

theorem fin15Anchored_clause18299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom2409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00713
  ] at hbad
  tauto

theorem fin15Anchored_clause18300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom2409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00713
  ] at hbad
  tauto

theorem fin15Anchored_clause18301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom2409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00713
  ] at hbad
  tauto

theorem fin15Anchored_clause18302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom2409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00713
  ] at hbad
  tauto

theorem fin15Anchored_clause18303 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom0621 Fin15AnchoredAtom0628
    Fin15AnchoredAtom0737 Fin15AnchoredAtom1408 Fin15AnchoredAtom2409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00713
  ] at hbad
  tauto

end ErdosSzekeres

end
