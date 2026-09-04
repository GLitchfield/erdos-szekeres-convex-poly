module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 166. -/

theorem fin15Anchored_clause21248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0957 Fin15AnchoredAtom3058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16474
  ] at hbad
  tauto

theorem fin15Anchored_clause21249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1342 Fin15AnchoredAtom3058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16474
  ] at hbad
  tauto

theorem fin15Anchored_clause21250 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom0895 Fin15AnchoredAtom0912
    Fin15AnchoredAtom0957 Fin15AnchoredAtom1342 Fin15AnchoredAtom3058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16474
  ] at hbad
  tauto

theorem fin15Anchored_clause21251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom3059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00410
  ] at hbad
  tauto

theorem fin15Anchored_clause21252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom3059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00410
  ] at hbad
  tauto

theorem fin15Anchored_clause21253 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom3059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00410
  ] at hbad
  tauto

theorem fin15Anchored_clause21254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0958 Fin15AnchoredAtom3059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00410
  ] at hbad
  tauto

theorem fin15Anchored_clause21255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3059 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom3059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00410
  ] at hbad
  tauto

theorem fin15Anchored_clause21256 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom0889 Fin15AnchoredAtom0913
    Fin15AnchoredAtom0958 Fin15AnchoredAtom1343 Fin15AnchoredAtom3059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00410
  ] at hbad
  tauto

theorem fin15Anchored_clause21257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom3060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00666
  ] at hbad
  tauto

theorem fin15Anchored_clause21258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom3060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00666
  ] at hbad
  tauto

theorem fin15Anchored_clause21259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom3060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00666
  ] at hbad
  tauto

theorem fin15Anchored_clause21260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom3060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00666
  ] at hbad
  tauto

theorem fin15Anchored_clause21261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom3060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00666
  ] at hbad
  tauto

theorem fin15Anchored_clause21262 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom0890 Fin15AnchoredAtom0914
    Fin15AnchoredAtom0959 Fin15AnchoredAtom1344 Fin15AnchoredAtom3060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00666
  ] at hbad
  tauto

theorem fin15Anchored_clause21263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom3061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01178
  ] at hbad
  tauto

theorem fin15Anchored_clause21264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom3061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01178
  ] at hbad
  tauto

theorem fin15Anchored_clause21265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom3061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01178
  ] at hbad
  tauto

theorem fin15Anchored_clause21266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom3061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01178
  ] at hbad
  tauto

theorem fin15Anchored_clause21267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom3061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01178
  ] at hbad
  tauto

theorem fin15Anchored_clause21268 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom0891 Fin15AnchoredAtom0915
    Fin15AnchoredAtom0960 Fin15AnchoredAtom1345 Fin15AnchoredAtom3061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01178
  ] at hbad
  tauto

theorem fin15Anchored_clause21269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3062 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom3062 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02202
  ] at hbad
  tauto

theorem fin15Anchored_clause21270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3062 chi ∧
      ¬Fin15AnchoredAtom0892 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0892 Fin15AnchoredAtom3062 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02202
  ] at hbad
  tauto

theorem fin15Anchored_clause21271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3062 chi ∧
      ¬Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0961 Fin15AnchoredAtom3062 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02202
  ] at hbad
  tauto

theorem fin15Anchored_clause21272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3062 chi ∧
      ¬Fin15AnchoredAtom1346 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1346 Fin15AnchoredAtom3062 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02202
  ] at hbad
  tauto

theorem fin15Anchored_clause21273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom3063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04250
  ] at hbad
  tauto

theorem fin15Anchored_clause21274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom3063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04250
  ] at hbad
  tauto

theorem fin15Anchored_clause21275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom3063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04250
  ] at hbad
  tauto

theorem fin15Anchored_clause21276 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom3063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04250
  ] at hbad
  tauto

theorem fin15Anchored_clause21277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom3063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04250
  ] at hbad
  tauto

theorem fin15Anchored_clause21278 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom0893 Fin15AnchoredAtom0917
    Fin15AnchoredAtom0962 Fin15AnchoredAtom1347 Fin15AnchoredAtom3063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04250
  ] at hbad
  tauto

theorem fin15Anchored_clause21279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom3064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08346
  ] at hbad
  tauto

theorem fin15Anchored_clause21280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0894 Fin15AnchoredAtom3064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08346
  ] at hbad
  tauto

theorem fin15Anchored_clause21281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom3064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08346
  ] at hbad
  tauto

theorem fin15Anchored_clause21282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom3064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08346
  ] at hbad
  tauto

theorem fin15Anchored_clause21283 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1348 Fin15AnchoredAtom3064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08346
  ] at hbad
  tauto

theorem fin15Anchored_clause21284 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom0894 Fin15AnchoredAtom0918
    Fin15AnchoredAtom0963 Fin15AnchoredAtom1348 Fin15AnchoredAtom3064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08346
  ] at hbad
  tauto

theorem fin15Anchored_clause21285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom3065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16538
  ] at hbad
  tauto

theorem fin15Anchored_clause21286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0895 Fin15AnchoredAtom3065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16538
  ] at hbad
  tauto

theorem fin15Anchored_clause21287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0919 Fin15AnchoredAtom3065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16538
  ] at hbad
  tauto

theorem fin15Anchored_clause21288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0964 Fin15AnchoredAtom3065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16538
  ] at hbad
  tauto

theorem fin15Anchored_clause21289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1349 Fin15AnchoredAtom3065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16538
  ] at hbad
  tauto

theorem fin15Anchored_clause21290 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom0895 Fin15AnchoredAtom0919
    Fin15AnchoredAtom0964 Fin15AnchoredAtom1349 Fin15AnchoredAtom3065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16538
  ] at hbad
  tauto

theorem fin15Anchored_clause21291 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom3066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00794
  ] at hbad
  tauto

theorem fin15Anchored_clause21292 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom3066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00794
  ] at hbad
  tauto

theorem fin15Anchored_clause21293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom3066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00794
  ] at hbad
  tauto

theorem fin15Anchored_clause21294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3066 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom3066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00794
  ] at hbad
  tauto

theorem fin15Anchored_clause21295 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3066 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom0890 Fin15AnchoredAtom0920
    Fin15AnchoredAtom0965 Fin15AnchoredAtom1350 Fin15AnchoredAtom3066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00794
  ] at hbad
  tauto

theorem fin15Anchored_clause21296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom3067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01306
  ] at hbad
  tauto

theorem fin15Anchored_clause21297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom3067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01306
  ] at hbad
  tauto

theorem fin15Anchored_clause21298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0921 Fin15AnchoredAtom3067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01306
  ] at hbad
  tauto

theorem fin15Anchored_clause21299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom3067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01306
  ] at hbad
  tauto

theorem fin15Anchored_clause21300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3067 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom3067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01306
  ] at hbad
  tauto

theorem fin15Anchored_clause21301 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom0891 Fin15AnchoredAtom0921
    Fin15AnchoredAtom0966 Fin15AnchoredAtom1351 Fin15AnchoredAtom3067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01306
  ] at hbad
  tauto

theorem fin15Anchored_clause21302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom3069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04378
  ] at hbad
  tauto

theorem fin15Anchored_clause21303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom3069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04378
  ] at hbad
  tauto

theorem fin15Anchored_clause21304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0968 Fin15AnchoredAtom3069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04378
  ] at hbad
  tauto

theorem fin15Anchored_clause21305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3069 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1353 Fin15AnchoredAtom3069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04378
  ] at hbad
  tauto

theorem fin15Anchored_clause21306 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom0893 Fin15AnchoredAtom0923
    Fin15AnchoredAtom0968 Fin15AnchoredAtom1353 Fin15AnchoredAtom3069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04378
  ] at hbad
  tauto

theorem fin15Anchored_clause21307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom3070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08474
  ] at hbad
  tauto

theorem fin15Anchored_clause21308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0894 Fin15AnchoredAtom3070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08474
  ] at hbad
  tauto

theorem fin15Anchored_clause21309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0924 Fin15AnchoredAtom3070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08474
  ] at hbad
  tauto

theorem fin15Anchored_clause21310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0969 Fin15AnchoredAtom3070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08474
  ] at hbad
  tauto

theorem fin15Anchored_clause21311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3070 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1354 Fin15AnchoredAtom3070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08474
  ] at hbad
  tauto

theorem fin15Anchored_clause21312 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom0894 Fin15AnchoredAtom0924
    Fin15AnchoredAtom0969 Fin15AnchoredAtom1354 Fin15AnchoredAtom3070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08474
  ] at hbad
  tauto

theorem fin15Anchored_clause21313 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom3071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16666
  ] at hbad
  tauto

theorem fin15Anchored_clause21314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0895 Fin15AnchoredAtom3071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16666
  ] at hbad
  tauto

theorem fin15Anchored_clause21315 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0925 Fin15AnchoredAtom3071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16666
  ] at hbad
  tauto

theorem fin15Anchored_clause21316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0970 Fin15AnchoredAtom3071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16666
  ] at hbad
  tauto

theorem fin15Anchored_clause21317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3071 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1355 Fin15AnchoredAtom3071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16666
  ] at hbad
  tauto

theorem fin15Anchored_clause21318 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3071 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom0895 Fin15AnchoredAtom0925
    Fin15AnchoredAtom0970 Fin15AnchoredAtom1355 Fin15AnchoredAtom3071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16666
  ] at hbad
  tauto

theorem fin15Anchored_clause21319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom3072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01562
  ] at hbad
  tauto

theorem fin15Anchored_clause21320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom3072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01562
  ] at hbad
  tauto

theorem fin15Anchored_clause21321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom3072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01562
  ] at hbad
  tauto

theorem fin15Anchored_clause21322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom3072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01562
  ] at hbad
  tauto

theorem fin15Anchored_clause21323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom3072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01562
  ] at hbad
  tauto

theorem fin15Anchored_clause21324 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom0891 Fin15AnchoredAtom0926
    Fin15AnchoredAtom0971 Fin15AnchoredAtom1356 Fin15AnchoredAtom3072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01562
  ] at hbad
  tauto

theorem fin15Anchored_clause21325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3073 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom3073 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02586
  ] at hbad
  tauto

theorem fin15Anchored_clause21326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3073 chi ∧
      ¬Fin15AnchoredAtom0972 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0972 Fin15AnchoredAtom3073 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02586
  ] at hbad
  tauto

theorem fin15Anchored_clause21327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3073 chi ∧
      ¬Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1357 Fin15AnchoredAtom3073 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02586
  ] at hbad
  tauto

theorem fin15Anchored_clause21328 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3073 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0892 chi ∧
      Fin15AnchoredAtom0927 chi ∧
      Fin15AnchoredAtom0972 chi ∧
      Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom0892 Fin15AnchoredAtom0927
    Fin15AnchoredAtom0972 Fin15AnchoredAtom1357 Fin15AnchoredAtom3073 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02586
  ] at hbad
  tauto

theorem fin15Anchored_clause21329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom3074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04634
  ] at hbad
  tauto

theorem fin15Anchored_clause21330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom3074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04634
  ] at hbad
  tauto

theorem fin15Anchored_clause21331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom3074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04634
  ] at hbad
  tauto

theorem fin15Anchored_clause21332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom3074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04634
  ] at hbad
  tauto

theorem fin15Anchored_clause21333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom3074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04634
  ] at hbad
  tauto

theorem fin15Anchored_clause21334 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom0893 Fin15AnchoredAtom0928
    Fin15AnchoredAtom0973 Fin15AnchoredAtom1358 Fin15AnchoredAtom3074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04634
  ] at hbad
  tauto

theorem fin15Anchored_clause21335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom3075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08730
  ] at hbad
  tauto

theorem fin15Anchored_clause21336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0894 Fin15AnchoredAtom3075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08730
  ] at hbad
  tauto

theorem fin15Anchored_clause21337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom3075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08730
  ] at hbad
  tauto

theorem fin15Anchored_clause21338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom3075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08730
  ] at hbad
  tauto

theorem fin15Anchored_clause21339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1359 Fin15AnchoredAtom3075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08730
  ] at hbad
  tauto

theorem fin15Anchored_clause21340 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom0894 Fin15AnchoredAtom0929
    Fin15AnchoredAtom0974 Fin15AnchoredAtom1359 Fin15AnchoredAtom3075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08730
  ] at hbad
  tauto

theorem fin15Anchored_clause21341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom3076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16922
  ] at hbad
  tauto

theorem fin15Anchored_clause21342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0895 Fin15AnchoredAtom3076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16922
  ] at hbad
  tauto

theorem fin15Anchored_clause21343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0930 Fin15AnchoredAtom3076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16922
  ] at hbad
  tauto

theorem fin15Anchored_clause21344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0975 Fin15AnchoredAtom3076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16922
  ] at hbad
  tauto

theorem fin15Anchored_clause21345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1360 Fin15AnchoredAtom3076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16922
  ] at hbad
  tauto

theorem fin15Anchored_clause21346 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom0895 Fin15AnchoredAtom0930
    Fin15AnchoredAtom0975 Fin15AnchoredAtom1360 Fin15AnchoredAtom3076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16922
  ] at hbad
  tauto

theorem fin15Anchored_clause21347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3077 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom3077 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03098
  ] at hbad
  tauto

theorem fin15Anchored_clause21348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3077 chi ∧
      ¬Fin15AnchoredAtom0892 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0892 Fin15AnchoredAtom3077 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03098
  ] at hbad
  tauto

theorem fin15Anchored_clause21349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom3078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05146
  ] at hbad
  tauto

theorem fin15Anchored_clause21350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom3078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05146
  ] at hbad
  tauto

theorem fin15Anchored_clause21351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom3078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05146
  ] at hbad
  tauto

theorem fin15Anchored_clause21352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom3078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05146
  ] at hbad
  tauto

theorem fin15Anchored_clause21353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom3078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05146
  ] at hbad
  tauto

theorem fin15Anchored_clause21354 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom0893 Fin15AnchoredAtom0932
    Fin15AnchoredAtom0977 Fin15AnchoredAtom1362 Fin15AnchoredAtom3078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05146
  ] at hbad
  tauto

theorem fin15Anchored_clause21355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom3079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09242
  ] at hbad
  tauto

theorem fin15Anchored_clause21356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0894 Fin15AnchoredAtom3079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09242
  ] at hbad
  tauto

theorem fin15Anchored_clause21357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom3079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09242
  ] at hbad
  tauto

theorem fin15Anchored_clause21358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0978 Fin15AnchoredAtom3079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09242
  ] at hbad
  tauto

theorem fin15Anchored_clause21359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom3079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09242
  ] at hbad
  tauto

theorem fin15Anchored_clause21360 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom0894 Fin15AnchoredAtom0933
    Fin15AnchoredAtom0978 Fin15AnchoredAtom1363 Fin15AnchoredAtom3079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09242
  ] at hbad
  tauto

theorem fin15Anchored_clause21361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom3080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17434
  ] at hbad
  tauto

theorem fin15Anchored_clause21362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0895 Fin15AnchoredAtom3080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17434
  ] at hbad
  tauto

theorem fin15Anchored_clause21363 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0934 Fin15AnchoredAtom3080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17434
  ] at hbad
  tauto

theorem fin15Anchored_clause21364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0979 Fin15AnchoredAtom3080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17434
  ] at hbad
  tauto

theorem fin15Anchored_clause21365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1364 Fin15AnchoredAtom3080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17434
  ] at hbad
  tauto

theorem fin15Anchored_clause21366 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom0895 Fin15AnchoredAtom0934
    Fin15AnchoredAtom0979 Fin15AnchoredAtom1364 Fin15AnchoredAtom3080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17434
  ] at hbad
  tauto

theorem fin15Anchored_clause21367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3081 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom3081 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06170
  ] at hbad
  tauto

theorem fin15Anchored_clause21368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3081 chi ∧
      ¬Fin15AnchoredAtom1365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1365 Fin15AnchoredAtom3081 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06170
  ] at hbad
  tauto

theorem fin15Anchored_clause21369 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3081 chi ∧
      Fin15AnchoredAtom0892 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0935 chi ∧
      Fin15AnchoredAtom0980 chi ∧
      Fin15AnchoredAtom1365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0892 Fin15AnchoredAtom0893 Fin15AnchoredAtom0935
    Fin15AnchoredAtom0980 Fin15AnchoredAtom1365 Fin15AnchoredAtom3081 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06170
  ] at hbad
  tauto

theorem fin15Anchored_clause21370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3082 chi ∧
      ¬Fin15AnchoredAtom0936 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0936 Fin15AnchoredAtom3082 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10266
  ] at hbad
  tauto

theorem fin15Anchored_clause21371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom3084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12314
  ] at hbad
  tauto

theorem fin15Anchored_clause21372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0894 Fin15AnchoredAtom3084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12314
  ] at hbad
  tauto

theorem fin15Anchored_clause21373 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom3084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12314
  ] at hbad
  tauto

theorem fin15Anchored_clause21374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom3084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12314
  ] at hbad
  tauto

theorem fin15Anchored_clause21375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1368 Fin15AnchoredAtom3084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12314
  ] at hbad
  tauto

end ErdosSzekeres

end
