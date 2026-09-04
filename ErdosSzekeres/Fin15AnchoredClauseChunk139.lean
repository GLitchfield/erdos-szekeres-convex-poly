module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 139. -/

theorem fin15Anchored_clause17792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom2314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12805
  ] at hbad
  tauto

theorem fin15Anchored_clause17793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0588 Fin15AnchoredAtom2314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12805
  ] at hbad
  tauto

theorem fin15Anchored_clause17794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0597 Fin15AnchoredAtom2314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12805
  ] at hbad
  tauto

theorem fin15Anchored_clause17795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom2314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12805
  ] at hbad
  tauto

theorem fin15Anchored_clause17796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1313 Fin15AnchoredAtom2314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12805
  ] at hbad
  tauto

theorem fin15Anchored_clause17797 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom0588 Fin15AnchoredAtom0597
    Fin15AnchoredAtom0807 Fin15AnchoredAtom1313 Fin15AnchoredAtom2314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12805
  ] at hbad
  tauto

theorem fin15Anchored_clause17798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom2315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20997
  ] at hbad
  tauto

theorem fin15Anchored_clause17799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0589 Fin15AnchoredAtom2315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20997
  ] at hbad
  tauto

theorem fin15Anchored_clause17800 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0598 Fin15AnchoredAtom2315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20997
  ] at hbad
  tauto

theorem fin15Anchored_clause17801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0808 Fin15AnchoredAtom2315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20997
  ] at hbad
  tauto

theorem fin15Anchored_clause17802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1314 Fin15AnchoredAtom2315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20997
  ] at hbad
  tauto

theorem fin15Anchored_clause17803 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom0589 Fin15AnchoredAtom0598
    Fin15AnchoredAtom0808 Fin15AnchoredAtom1314 Fin15AnchoredAtom2315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20997
  ] at hbad
  tauto

theorem fin15Anchored_clause17804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0588 Fin15AnchoredAtom2316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25093
  ] at hbad
  tauto

theorem fin15Anchored_clause17805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0589 Fin15AnchoredAtom2316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25093
  ] at hbad
  tauto

theorem fin15Anchored_clause17806 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0599 Fin15AnchoredAtom2316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25093
  ] at hbad
  tauto

theorem fin15Anchored_clause17807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0809 Fin15AnchoredAtom2316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25093
  ] at hbad
  tauto

theorem fin15Anchored_clause17808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1315 Fin15AnchoredAtom2316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25093
  ] at hbad
  tauto

theorem fin15Anchored_clause17809 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0588 Fin15AnchoredAtom0589 Fin15AnchoredAtom0599
    Fin15AnchoredAtom0809 Fin15AnchoredAtom1315 Fin15AnchoredAtom2316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25093
  ] at hbad
  tauto

theorem fin15Anchored_clause17810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2317 chi ∧
      ¬Fin15AnchoredAtom0590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0590 Fin15AnchoredAtom2317 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07173
  ] at hbad
  tauto

theorem fin15Anchored_clause17811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2317 chi ∧
      ¬Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom2317 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07173
  ] at hbad
  tauto

theorem fin15Anchored_clause17812 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2317 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0590 Fin15AnchoredAtom0591 Fin15AnchoredAtom0594
    Fin15AnchoredAtom0810 Fin15AnchoredAtom1316 Fin15AnchoredAtom2317 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07173
  ] at hbad
  tauto

theorem fin15Anchored_clause17813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom0590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0590 Fin15AnchoredAtom2318 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11269
  ] at hbad
  tauto

theorem fin15Anchored_clause17814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0592 Fin15AnchoredAtom2318 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11269
  ] at hbad
  tauto

theorem fin15Anchored_clause17815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom0595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0595 Fin15AnchoredAtom2318 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11269
  ] at hbad
  tauto

theorem fin15Anchored_clause17816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0811 Fin15AnchoredAtom2318 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11269
  ] at hbad
  tauto

theorem fin15Anchored_clause17817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2318 chi ∧
      ¬Fin15AnchoredAtom1317 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1317 Fin15AnchoredAtom2318 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11269
  ] at hbad
  tauto

theorem fin15Anchored_clause17818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2319 chi ∧
      ¬Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0593 Fin15AnchoredAtom2319 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19461
  ] at hbad
  tauto

theorem fin15Anchored_clause17819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom2320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13317
  ] at hbad
  tauto

theorem fin15Anchored_clause17820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0592 Fin15AnchoredAtom2320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13317
  ] at hbad
  tauto

theorem fin15Anchored_clause17821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0597 Fin15AnchoredAtom2320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13317
  ] at hbad
  tauto

theorem fin15Anchored_clause17822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom2320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13317
  ] at hbad
  tauto

theorem fin15Anchored_clause17823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom2320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13317
  ] at hbad
  tauto

theorem fin15Anchored_clause17824 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom0592 Fin15AnchoredAtom0597
    Fin15AnchoredAtom0813 Fin15AnchoredAtom1319 Fin15AnchoredAtom2320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13317
  ] at hbad
  tauto

theorem fin15Anchored_clause17825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom2321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21509
  ] at hbad
  tauto

theorem fin15Anchored_clause17826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0593 Fin15AnchoredAtom2321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21509
  ] at hbad
  tauto

theorem fin15Anchored_clause17827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0598 Fin15AnchoredAtom2321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21509
  ] at hbad
  tauto

theorem fin15Anchored_clause17828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0814 Fin15AnchoredAtom2321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21509
  ] at hbad
  tauto

theorem fin15Anchored_clause17829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1320 Fin15AnchoredAtom2321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21509
  ] at hbad
  tauto

theorem fin15Anchored_clause17830 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom0593 Fin15AnchoredAtom0598
    Fin15AnchoredAtom0814 Fin15AnchoredAtom1320 Fin15AnchoredAtom2321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21509
  ] at hbad
  tauto

theorem fin15Anchored_clause17831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0592 Fin15AnchoredAtom2322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25605
  ] at hbad
  tauto

theorem fin15Anchored_clause17832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0593 Fin15AnchoredAtom2322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25605
  ] at hbad
  tauto

theorem fin15Anchored_clause17833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0599 Fin15AnchoredAtom2322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25605
  ] at hbad
  tauto

theorem fin15Anchored_clause17834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0815 Fin15AnchoredAtom2322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25605
  ] at hbad
  tauto

theorem fin15Anchored_clause17835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1321 Fin15AnchoredAtom2322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25605
  ] at hbad
  tauto

theorem fin15Anchored_clause17836 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0592 Fin15AnchoredAtom0593 Fin15AnchoredAtom0599
    Fin15AnchoredAtom0815 Fin15AnchoredAtom1321 Fin15AnchoredAtom2322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25605
  ] at hbad
  tauto

theorem fin15Anchored_clause17837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2323 chi ∧
      ¬Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0597 Fin15AnchoredAtom2323 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14341
  ] at hbad
  tauto

theorem fin15Anchored_clause17838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2323 chi ∧
      ¬Fin15AnchoredAtom0816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0816 Fin15AnchoredAtom2323 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14341
  ] at hbad
  tauto

theorem fin15Anchored_clause17839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2324 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0598 Fin15AnchoredAtom2324 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22533
  ] at hbad
  tauto

theorem fin15Anchored_clause17840 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2324 chi ∧
      ¬Fin15AnchoredAtom0817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0817 Fin15AnchoredAtom2324 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22533
  ] at hbad
  tauto

theorem fin15Anchored_clause17841 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2324 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0594 Fin15AnchoredAtom0596 Fin15AnchoredAtom0598
    Fin15AnchoredAtom0817 Fin15AnchoredAtom1323 Fin15AnchoredAtom2324 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22533
  ] at hbad
  tauto

theorem fin15Anchored_clause17842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2325 chi ∧
      ¬Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0599 Fin15AnchoredAtom2325 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26629
  ] at hbad
  tauto

theorem fin15Anchored_clause17843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0597 Fin15AnchoredAtom2326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28677
  ] at hbad
  tauto

theorem fin15Anchored_clause17844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0598 Fin15AnchoredAtom2326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28677
  ] at hbad
  tauto

theorem fin15Anchored_clause17845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0599 Fin15AnchoredAtom2326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28677
  ] at hbad
  tauto

theorem fin15Anchored_clause17846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0819 Fin15AnchoredAtom2326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28677
  ] at hbad
  tauto

theorem fin15Anchored_clause17847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1325 Fin15AnchoredAtom2326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28677
  ] at hbad
  tauto

theorem fin15Anchored_clause17848 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0597 Fin15AnchoredAtom0598 Fin15AnchoredAtom0599
    Fin15AnchoredAtom0819 Fin15AnchoredAtom1325 Fin15AnchoredAtom2326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28677
  ] at hbad
  tauto

theorem fin15Anchored_clause17849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom2327 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00121
  ] at hbad
  tauto

theorem fin15Anchored_clause17850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom2327 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00121
  ] at hbad
  tauto

theorem fin15Anchored_clause17851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom2327 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00121
  ] at hbad
  tauto

theorem fin15Anchored_clause17852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom2327 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00121
  ] at hbad
  tauto

theorem fin15Anchored_clause17853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom2327 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00121
  ] at hbad
  tauto

theorem fin15Anchored_clause17854 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom0601 Fin15AnchoredAtom0610
    Fin15AnchoredAtom0655 Fin15AnchoredAtom1326 Fin15AnchoredAtom2327 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00121
  ] at hbad
  tauto

theorem fin15Anchored_clause17855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom2328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00185
  ] at hbad
  tauto

theorem fin15Anchored_clause17856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom2328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00185
  ] at hbad
  tauto

theorem fin15Anchored_clause17857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom2328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00185
  ] at hbad
  tauto

theorem fin15Anchored_clause17858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom2328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00185
  ] at hbad
  tauto

theorem fin15Anchored_clause17859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom2328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00185
  ] at hbad
  tauto

theorem fin15Anchored_clause17860 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom0602 Fin15AnchoredAtom0611
    Fin15AnchoredAtom0656 Fin15AnchoredAtom1327 Fin15AnchoredAtom2328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00185
  ] at hbad
  tauto

theorem fin15Anchored_clause17861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom2329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00313
  ] at hbad
  tauto

theorem fin15Anchored_clause17862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom0603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom2329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00313
  ] at hbad
  tauto

theorem fin15Anchored_clause17863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom2329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00313
  ] at hbad
  tauto

theorem fin15Anchored_clause17864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom0657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom2329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00313
  ] at hbad
  tauto

theorem fin15Anchored_clause17865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2329 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom2329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00313
  ] at hbad
  tauto

theorem fin15Anchored_clause17866 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom0603 Fin15AnchoredAtom0612
    Fin15AnchoredAtom0657 Fin15AnchoredAtom1328 Fin15AnchoredAtom2329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00313
  ] at hbad
  tauto

theorem fin15Anchored_clause17867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom2330 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00569
  ] at hbad
  tauto

theorem fin15Anchored_clause17868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom2330 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00569
  ] at hbad
  tauto

theorem fin15Anchored_clause17869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom2330 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00569
  ] at hbad
  tauto

theorem fin15Anchored_clause17870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom2330 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00569
  ] at hbad
  tauto

theorem fin15Anchored_clause17871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom2330 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00569
  ] at hbad
  tauto

theorem fin15Anchored_clause17872 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom0604 Fin15AnchoredAtom0613
    Fin15AnchoredAtom0658 Fin15AnchoredAtom1329 Fin15AnchoredAtom2330 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00569
  ] at hbad
  tauto

theorem fin15Anchored_clause17873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom2331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01081
  ] at hbad
  tauto

theorem fin15Anchored_clause17874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom2331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01081
  ] at hbad
  tauto

theorem fin15Anchored_clause17875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom2331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01081
  ] at hbad
  tauto

theorem fin15Anchored_clause17876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom2331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01081
  ] at hbad
  tauto

theorem fin15Anchored_clause17877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom2331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01081
  ] at hbad
  tauto

theorem fin15Anchored_clause17878 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom0605 Fin15AnchoredAtom0614
    Fin15AnchoredAtom0659 Fin15AnchoredAtom1330 Fin15AnchoredAtom2331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01081
  ] at hbad
  tauto

theorem fin15Anchored_clause17879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom2332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02105
  ] at hbad
  tauto

theorem fin15Anchored_clause17880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom0606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0606 Fin15AnchoredAtom2332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02105
  ] at hbad
  tauto

theorem fin15Anchored_clause17881 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom0615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0615 Fin15AnchoredAtom2332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02105
  ] at hbad
  tauto

theorem fin15Anchored_clause17882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom0660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0660 Fin15AnchoredAtom2332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02105
  ] at hbad
  tauto

theorem fin15Anchored_clause17883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2332 chi ∧
      ¬Fin15AnchoredAtom1331 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1331 Fin15AnchoredAtom2332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02105
  ] at hbad
  tauto

theorem fin15Anchored_clause17884 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2332 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom1331 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom0606 Fin15AnchoredAtom0615
    Fin15AnchoredAtom0660 Fin15AnchoredAtom1331 Fin15AnchoredAtom2332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02105
  ] at hbad
  tauto

theorem fin15Anchored_clause17885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom2333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04153
  ] at hbad
  tauto

theorem fin15Anchored_clause17886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom2333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04153
  ] at hbad
  tauto

theorem fin15Anchored_clause17887 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom2333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04153
  ] at hbad
  tauto

theorem fin15Anchored_clause17888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom2333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04153
  ] at hbad
  tauto

theorem fin15Anchored_clause17889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom2333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04153
  ] at hbad
  tauto

theorem fin15Anchored_clause17890 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom0607 Fin15AnchoredAtom0616
    Fin15AnchoredAtom0661 Fin15AnchoredAtom1332 Fin15AnchoredAtom2333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04153
  ] at hbad
  tauto

theorem fin15Anchored_clause17891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom2334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08249
  ] at hbad
  tauto

theorem fin15Anchored_clause17892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom2334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08249
  ] at hbad
  tauto

theorem fin15Anchored_clause17893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom2334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08249
  ] at hbad
  tauto

theorem fin15Anchored_clause17894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0662 Fin15AnchoredAtom2334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08249
  ] at hbad
  tauto

theorem fin15Anchored_clause17895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom2334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08249
  ] at hbad
  tauto

theorem fin15Anchored_clause17896 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom0608 Fin15AnchoredAtom0617
    Fin15AnchoredAtom0662 Fin15AnchoredAtom1333 Fin15AnchoredAtom2334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08249
  ] at hbad
  tauto

theorem fin15Anchored_clause17897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom2335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16441
  ] at hbad
  tauto

theorem fin15Anchored_clause17898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0609 Fin15AnchoredAtom2335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16441
  ] at hbad
  tauto

theorem fin15Anchored_clause17899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0618 Fin15AnchoredAtom2335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16441
  ] at hbad
  tauto

theorem fin15Anchored_clause17900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0663 Fin15AnchoredAtom2335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16441
  ] at hbad
  tauto

theorem fin15Anchored_clause17901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1334 Fin15AnchoredAtom2335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16441
  ] at hbad
  tauto

theorem fin15Anchored_clause17902 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom0609 Fin15AnchoredAtom0618
    Fin15AnchoredAtom0663 Fin15AnchoredAtom1334 Fin15AnchoredAtom2335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16441
  ] at hbad
  tauto

theorem fin15Anchored_clause17903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom2336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00217
  ] at hbad
  tauto

theorem fin15Anchored_clause17904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom2336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00217
  ] at hbad
  tauto

theorem fin15Anchored_clause17905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom2336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00217
  ] at hbad
  tauto

theorem fin15Anchored_clause17906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom2336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00217
  ] at hbad
  tauto

theorem fin15Anchored_clause17907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom2336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00217
  ] at hbad
  tauto

theorem fin15Anchored_clause17908 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom0602 Fin15AnchoredAtom0619
    Fin15AnchoredAtom0664 Fin15AnchoredAtom1335 Fin15AnchoredAtom2336 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00217
  ] at hbad
  tauto

theorem fin15Anchored_clause17909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom2337 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00345
  ] at hbad
  tauto

theorem fin15Anchored_clause17910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom0603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom2337 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00345
  ] at hbad
  tauto

theorem fin15Anchored_clause17911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom2337 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00345
  ] at hbad
  tauto

theorem fin15Anchored_clause17912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom2337 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00345
  ] at hbad
  tauto

theorem fin15Anchored_clause17913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2337 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom2337 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00345
  ] at hbad
  tauto

theorem fin15Anchored_clause17914 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom0603 Fin15AnchoredAtom0620
    Fin15AnchoredAtom0665 Fin15AnchoredAtom1336 Fin15AnchoredAtom2337 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00345
  ] at hbad
  tauto

theorem fin15Anchored_clause17915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom2338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00601
  ] at hbad
  tauto

theorem fin15Anchored_clause17916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom2338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00601
  ] at hbad
  tauto

theorem fin15Anchored_clause17917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom2338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00601
  ] at hbad
  tauto

theorem fin15Anchored_clause17918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom2338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00601
  ] at hbad
  tauto

theorem fin15Anchored_clause17919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom2338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00601
  ] at hbad
  tauto

end ErdosSzekeres

end
