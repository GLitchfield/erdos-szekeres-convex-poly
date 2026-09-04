module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 158. -/

theorem fin15Anchored_clause20224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom0798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0798 Fin15AnchoredAtom2801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21761
  ] at hbad
  tauto

theorem fin15Anchored_clause20225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0814 Fin15AnchoredAtom2801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21761
  ] at hbad
  tauto

theorem fin15Anchored_clause20226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2801 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1800 Fin15AnchoredAtom2801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21761
  ] at hbad
  tauto

theorem fin15Anchored_clause20227 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0791 Fin15AnchoredAtom0793 Fin15AnchoredAtom0798
    Fin15AnchoredAtom0814 Fin15AnchoredAtom1800 Fin15AnchoredAtom2801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21761
  ] at hbad
  tauto

theorem fin15Anchored_clause20228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0792 Fin15AnchoredAtom2802 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25857
  ] at hbad
  tauto

theorem fin15Anchored_clause20229 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom0793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0793 Fin15AnchoredAtom2802 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25857
  ] at hbad
  tauto

theorem fin15Anchored_clause20230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom0799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0799 Fin15AnchoredAtom2802 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25857
  ] at hbad
  tauto

theorem fin15Anchored_clause20231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0815 Fin15AnchoredAtom2802 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25857
  ] at hbad
  tauto

theorem fin15Anchored_clause20232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2802 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1801 Fin15AnchoredAtom2802 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25857
  ] at hbad
  tauto

theorem fin15Anchored_clause20233 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0792 Fin15AnchoredAtom0793 Fin15AnchoredAtom0799
    Fin15AnchoredAtom0815 Fin15AnchoredAtom1801 Fin15AnchoredAtom2802 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25857
  ] at hbad
  tauto

theorem fin15Anchored_clause20234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0797 Fin15AnchoredAtom2806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28929
  ] at hbad
  tauto

theorem fin15Anchored_clause20235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom0798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0798 Fin15AnchoredAtom2806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28929
  ] at hbad
  tauto

theorem fin15Anchored_clause20236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom0799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0799 Fin15AnchoredAtom2806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28929
  ] at hbad
  tauto

theorem fin15Anchored_clause20237 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2806 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0819 Fin15AnchoredAtom2806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28929
  ] at hbad
  tauto

theorem fin15Anchored_clause20238 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0797 Fin15AnchoredAtom0798 Fin15AnchoredAtom0799
    Fin15AnchoredAtom0819 Fin15AnchoredAtom1805 Fin15AnchoredAtom2806 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28929
  ] at hbad
  tauto

theorem fin15Anchored_clause20239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom2807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07681
  ] at hbad
  tauto

theorem fin15Anchored_clause20240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom2807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07681
  ] at hbad
  tauto

theorem fin15Anchored_clause20241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom0804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0804 Fin15AnchoredAtom2807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07681
  ] at hbad
  tauto

theorem fin15Anchored_clause20242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom0810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0810 Fin15AnchoredAtom2807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07681
  ] at hbad
  tauto

theorem fin15Anchored_clause20243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2807 chi ∧
      ¬Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1806 Fin15AnchoredAtom2807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07681
  ] at hbad
  tauto

theorem fin15Anchored_clause20244 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2807 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom0801 Fin15AnchoredAtom0804
    Fin15AnchoredAtom0810 Fin15AnchoredAtom1806 Fin15AnchoredAtom2807 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07681
  ] at hbad
  tauto

theorem fin15Anchored_clause20245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom2808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11777
  ] at hbad
  tauto

theorem fin15Anchored_clause20246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom2808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11777
  ] at hbad
  tauto

theorem fin15Anchored_clause20247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom0805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0805 Fin15AnchoredAtom2808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11777
  ] at hbad
  tauto

theorem fin15Anchored_clause20248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0811 Fin15AnchoredAtom2808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11777
  ] at hbad
  tauto

theorem fin15Anchored_clause20249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2808 chi ∧
      ¬Fin15AnchoredAtom1807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1807 Fin15AnchoredAtom2808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11777
  ] at hbad
  tauto

theorem fin15Anchored_clause20250 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2808 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom0802 Fin15AnchoredAtom0805
    Fin15AnchoredAtom0811 Fin15AnchoredAtom1807 Fin15AnchoredAtom2808 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11777
  ] at hbad
  tauto

theorem fin15Anchored_clause20251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom2809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19969
  ] at hbad
  tauto

theorem fin15Anchored_clause20252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0803 Fin15AnchoredAtom2809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19969
  ] at hbad
  tauto

theorem fin15Anchored_clause20253 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom0806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0806 Fin15AnchoredAtom2809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19969
  ] at hbad
  tauto

theorem fin15Anchored_clause20254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom0812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0812 Fin15AnchoredAtom2809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19969
  ] at hbad
  tauto

theorem fin15Anchored_clause20255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2809 chi ∧
      ¬Fin15AnchoredAtom1808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1808 Fin15AnchoredAtom2809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19969
  ] at hbad
  tauto

theorem fin15Anchored_clause20256 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2809 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom1808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom0803 Fin15AnchoredAtom0806
    Fin15AnchoredAtom0812 Fin15AnchoredAtom1808 Fin15AnchoredAtom2809 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19969
  ] at hbad
  tauto

theorem fin15Anchored_clause20257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom2810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13825
  ] at hbad
  tauto

theorem fin15Anchored_clause20258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom2810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13825
  ] at hbad
  tauto

theorem fin15Anchored_clause20259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom2810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13825
  ] at hbad
  tauto

theorem fin15Anchored_clause20260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom2810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13825
  ] at hbad
  tauto

theorem fin15Anchored_clause20261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2810 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom2810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13825
  ] at hbad
  tauto

theorem fin15Anchored_clause20262 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom0802 Fin15AnchoredAtom0807
    Fin15AnchoredAtom0813 Fin15AnchoredAtom1809 Fin15AnchoredAtom2810 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13825
  ] at hbad
  tauto

theorem fin15Anchored_clause20263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom2811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22017
  ] at hbad
  tauto

theorem fin15Anchored_clause20264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0803 Fin15AnchoredAtom2811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22017
  ] at hbad
  tauto

theorem fin15Anchored_clause20265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0808 Fin15AnchoredAtom2811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22017
  ] at hbad
  tauto

theorem fin15Anchored_clause20266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0814 Fin15AnchoredAtom2811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22017
  ] at hbad
  tauto

theorem fin15Anchored_clause20267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2811 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1810 Fin15AnchoredAtom2811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22017
  ] at hbad
  tauto

theorem fin15Anchored_clause20268 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom0803 Fin15AnchoredAtom0808
    Fin15AnchoredAtom0814 Fin15AnchoredAtom1810 Fin15AnchoredAtom2811 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22017
  ] at hbad
  tauto

theorem fin15Anchored_clause20269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom2812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26113
  ] at hbad
  tauto

theorem fin15Anchored_clause20270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0803 Fin15AnchoredAtom2812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26113
  ] at hbad
  tauto

theorem fin15Anchored_clause20271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0809 Fin15AnchoredAtom2812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26113
  ] at hbad
  tauto

theorem fin15Anchored_clause20272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0815 Fin15AnchoredAtom2812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26113
  ] at hbad
  tauto

theorem fin15Anchored_clause20273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2812 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1811 Fin15AnchoredAtom2812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26113
  ] at hbad
  tauto

theorem fin15Anchored_clause20274 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom0803 Fin15AnchoredAtom0809
    Fin15AnchoredAtom0815 Fin15AnchoredAtom1811 Fin15AnchoredAtom2812 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26113
  ] at hbad
  tauto

theorem fin15Anchored_clause20275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2813 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom2813 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14849
  ] at hbad
  tauto

theorem fin15Anchored_clause20276 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2813 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0804 Fin15AnchoredAtom0805 Fin15AnchoredAtom0807
    Fin15AnchoredAtom0816 Fin15AnchoredAtom1812 Fin15AnchoredAtom2813 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14849
  ] at hbad
  tauto

theorem fin15Anchored_clause20277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2814 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0808 Fin15AnchoredAtom2814 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23041
  ] at hbad
  tauto

theorem fin15Anchored_clause20278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2814 chi ∧
      ¬Fin15AnchoredAtom0817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0817 Fin15AnchoredAtom2814 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23041
  ] at hbad
  tauto

theorem fin15Anchored_clause20279 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2814 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0804 Fin15AnchoredAtom0806 Fin15AnchoredAtom0808
    Fin15AnchoredAtom0817 Fin15AnchoredAtom1813 Fin15AnchoredAtom2814 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23041
  ] at hbad
  tauto

theorem fin15Anchored_clause20280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2815 chi ∧
      ¬Fin15AnchoredAtom0805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0805 Fin15AnchoredAtom2815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27137
  ] at hbad
  tauto

theorem fin15Anchored_clause20281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2815 chi ∧
      ¬Fin15AnchoredAtom0806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0806 Fin15AnchoredAtom2815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27137
  ] at hbad
  tauto

theorem fin15Anchored_clause20282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2815 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0809 Fin15AnchoredAtom2815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27137
  ] at hbad
  tauto

theorem fin15Anchored_clause20283 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2815 chi ∧
      ¬Fin15AnchoredAtom0818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0818 Fin15AnchoredAtom2815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27137
  ] at hbad
  tauto

theorem fin15Anchored_clause20284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2815 chi ∧
      ¬Fin15AnchoredAtom1814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1814 Fin15AnchoredAtom2815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27137
  ] at hbad
  tauto

theorem fin15Anchored_clause20285 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2815 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom0818 chi ∧
      Fin15AnchoredAtom1814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0805 Fin15AnchoredAtom0806 Fin15AnchoredAtom0809
    Fin15AnchoredAtom0818 Fin15AnchoredAtom1814 Fin15AnchoredAtom2815 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27137
  ] at hbad
  tauto

theorem fin15Anchored_clause20286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom2816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29185
  ] at hbad
  tauto

theorem fin15Anchored_clause20287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0808 Fin15AnchoredAtom2816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29185
  ] at hbad
  tauto

theorem fin15Anchored_clause20288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0809 Fin15AnchoredAtom2816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29185
  ] at hbad
  tauto

theorem fin15Anchored_clause20289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0819 Fin15AnchoredAtom2816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29185
  ] at hbad
  tauto

theorem fin15Anchored_clause20290 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2816 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1815 Fin15AnchoredAtom2816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29185
  ] at hbad
  tauto

theorem fin15Anchored_clause20291 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom0808 Fin15AnchoredAtom0809
    Fin15AnchoredAtom0819 Fin15AnchoredAtom1815 Fin15AnchoredAtom2816 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29185
  ] at hbad
  tauto

theorem fin15Anchored_clause20292 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom0810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0810 Fin15AnchoredAtom2817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15361
  ] at hbad
  tauto

theorem fin15Anchored_clause20293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0811 Fin15AnchoredAtom2817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15361
  ] at hbad
  tauto

theorem fin15Anchored_clause20294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom2817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15361
  ] at hbad
  tauto

theorem fin15Anchored_clause20295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom0816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0816 Fin15AnchoredAtom2817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15361
  ] at hbad
  tauto

theorem fin15Anchored_clause20296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2817 chi ∧
      ¬Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1816 Fin15AnchoredAtom2817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15361
  ] at hbad
  tauto

theorem fin15Anchored_clause20297 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2817 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0810 Fin15AnchoredAtom0811 Fin15AnchoredAtom0813
    Fin15AnchoredAtom0816 Fin15AnchoredAtom1816 Fin15AnchoredAtom2817 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15361
  ] at hbad
  tauto

theorem fin15Anchored_clause20298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom0810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0810 Fin15AnchoredAtom2818 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23553
  ] at hbad
  tauto

theorem fin15Anchored_clause20299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom0812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0812 Fin15AnchoredAtom2818 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23553
  ] at hbad
  tauto

theorem fin15Anchored_clause20300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0814 Fin15AnchoredAtom2818 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23553
  ] at hbad
  tauto

theorem fin15Anchored_clause20301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom0817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0817 Fin15AnchoredAtom2818 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23553
  ] at hbad
  tauto

theorem fin15Anchored_clause20302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2818 chi ∧
      ¬Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1817 Fin15AnchoredAtom2818 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23553
  ] at hbad
  tauto

theorem fin15Anchored_clause20303 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2818 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0810 Fin15AnchoredAtom0812 Fin15AnchoredAtom0814
    Fin15AnchoredAtom0817 Fin15AnchoredAtom1817 Fin15AnchoredAtom2818 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23553
  ] at hbad
  tauto

theorem fin15Anchored_clause20304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2819 chi ∧
      ¬Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0811 Fin15AnchoredAtom2819 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27649
  ] at hbad
  tauto

theorem fin15Anchored_clause20305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2819 chi ∧
      ¬Fin15AnchoredAtom0812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0812 Fin15AnchoredAtom2819 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27649
  ] at hbad
  tauto

theorem fin15Anchored_clause20306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2819 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0815 Fin15AnchoredAtom2819 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27649
  ] at hbad
  tauto

theorem fin15Anchored_clause20307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2819 chi ∧
      ¬Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1818 Fin15AnchoredAtom2819 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27649
  ] at hbad
  tauto

theorem fin15Anchored_clause20308 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2819 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom0818 chi ∧
      Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0811 Fin15AnchoredAtom0812 Fin15AnchoredAtom0815
    Fin15AnchoredAtom0818 Fin15AnchoredAtom1818 Fin15AnchoredAtom2819 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27649
  ] at hbad
  tauto

theorem fin15Anchored_clause20309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom2820 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29697
  ] at hbad
  tauto

theorem fin15Anchored_clause20310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0814 Fin15AnchoredAtom2820 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29697
  ] at hbad
  tauto

theorem fin15Anchored_clause20311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0815 Fin15AnchoredAtom2820 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29697
  ] at hbad
  tauto

theorem fin15Anchored_clause20312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0819 Fin15AnchoredAtom2820 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29697
  ] at hbad
  tauto

theorem fin15Anchored_clause20313 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2820 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1819 Fin15AnchoredAtom2820 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29697
  ] at hbad
  tauto

theorem fin15Anchored_clause20314 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom0814 Fin15AnchoredAtom0815
    Fin15AnchoredAtom0819 Fin15AnchoredAtom1819 Fin15AnchoredAtom2820 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29697
  ] at hbad
  tauto

theorem fin15Anchored_clause20315 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2821 chi ∧
      ¬Fin15AnchoredAtom0816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0816 Fin15AnchoredAtom2821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30721
  ] at hbad
  tauto

theorem fin15Anchored_clause20316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2821 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0819 Fin15AnchoredAtom2821 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30721
  ] at hbad
  tauto

theorem fin15Anchored_clause20317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom2822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00062
  ] at hbad
  tauto

theorem fin15Anchored_clause20318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom2822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00062
  ] at hbad
  tauto

theorem fin15Anchored_clause20319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom2822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00062
  ] at hbad
  tauto

theorem fin15Anchored_clause20320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom2822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00062
  ] at hbad
  tauto

theorem fin15Anchored_clause20321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1106 Fin15AnchoredAtom2822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00062
  ] at hbad
  tauto

theorem fin15Anchored_clause20322 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom1106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom0821 Fin15AnchoredAtom0831
    Fin15AnchoredAtom0886 Fin15AnchoredAtom1106 Fin15AnchoredAtom2822 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00062
  ] at hbad
  tauto

theorem fin15Anchored_clause20323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom2823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00094
  ] at hbad
  tauto

theorem fin15Anchored_clause20324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom2823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00094
  ] at hbad
  tauto

theorem fin15Anchored_clause20325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom2823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00094
  ] at hbad
  tauto

theorem fin15Anchored_clause20326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom2823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00094
  ] at hbad
  tauto

theorem fin15Anchored_clause20327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1107 Fin15AnchoredAtom2823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00094
  ] at hbad
  tauto

theorem fin15Anchored_clause20328 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom1107 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom0822 Fin15AnchoredAtom0832
    Fin15AnchoredAtom0887 Fin15AnchoredAtom1107 Fin15AnchoredAtom2823 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00094
  ] at hbad
  tauto

theorem fin15Anchored_clause20329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom2824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00158
  ] at hbad
  tauto

theorem fin15Anchored_clause20330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom2824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00158
  ] at hbad
  tauto

theorem fin15Anchored_clause20331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom2824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00158
  ] at hbad
  tauto

theorem fin15Anchored_clause20332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom2824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00158
  ] at hbad
  tauto

theorem fin15Anchored_clause20333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1108 Fin15AnchoredAtom2824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00158
  ] at hbad
  tauto

theorem fin15Anchored_clause20334 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom1108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom0823 Fin15AnchoredAtom0833
    Fin15AnchoredAtom0888 Fin15AnchoredAtom1108 Fin15AnchoredAtom2824 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00158
  ] at hbad
  tauto

theorem fin15Anchored_clause20335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2825 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom2825 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00286
  ] at hbad
  tauto

theorem fin15Anchored_clause20336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom2826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00542
  ] at hbad
  tauto

theorem fin15Anchored_clause20337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom2826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00542
  ] at hbad
  tauto

theorem fin15Anchored_clause20338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom2826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00542
  ] at hbad
  tauto

theorem fin15Anchored_clause20339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom2826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00542
  ] at hbad
  tauto

theorem fin15Anchored_clause20340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom2826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00542
  ] at hbad
  tauto

theorem fin15Anchored_clause20341 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom0825 Fin15AnchoredAtom0835
    Fin15AnchoredAtom0890 Fin15AnchoredAtom1110 Fin15AnchoredAtom2826 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00542
  ] at hbad
  tauto

theorem fin15Anchored_clause20342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom2827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01054
  ] at hbad
  tauto

theorem fin15Anchored_clause20343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom2827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01054
  ] at hbad
  tauto

theorem fin15Anchored_clause20344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom2827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01054
  ] at hbad
  tauto

theorem fin15Anchored_clause20345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom2827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01054
  ] at hbad
  tauto

theorem fin15Anchored_clause20346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom2827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01054
  ] at hbad
  tauto

theorem fin15Anchored_clause20347 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom0826 Fin15AnchoredAtom0836
    Fin15AnchoredAtom0891 Fin15AnchoredAtom1111 Fin15AnchoredAtom2827 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01054
  ] at hbad
  tauto

theorem fin15Anchored_clause20348 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2828 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0827 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0892 chi ∧
      Fin15AnchoredAtom1112 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom0827 Fin15AnchoredAtom0837
    Fin15AnchoredAtom0892 Fin15AnchoredAtom1112 Fin15AnchoredAtom2828 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02078
  ] at hbad
  tauto

theorem fin15Anchored_clause20349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom2829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04126
  ] at hbad
  tauto

theorem fin15Anchored_clause20350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom2829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04126
  ] at hbad
  tauto

theorem fin15Anchored_clause20351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom2829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04126
  ] at hbad
  tauto

end ErdosSzekeres

end
