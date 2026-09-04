module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 167. -/

theorem fin15Anchored_clause21376 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom0894 Fin15AnchoredAtom0938
    Fin15AnchoredAtom0983 Fin15AnchoredAtom1368 Fin15AnchoredAtom3084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12314
  ] at hbad
  tauto

theorem fin15Anchored_clause21377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom3085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20506
  ] at hbad
  tauto

theorem fin15Anchored_clause21378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0895 Fin15AnchoredAtom3085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20506
  ] at hbad
  tauto

theorem fin15Anchored_clause21379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0939 Fin15AnchoredAtom3085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20506
  ] at hbad
  tauto

theorem fin15Anchored_clause21380 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0984 Fin15AnchoredAtom3085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20506
  ] at hbad
  tauto

theorem fin15Anchored_clause21381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1369 Fin15AnchoredAtom3085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20506
  ] at hbad
  tauto

theorem fin15Anchored_clause21382 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom0895 Fin15AnchoredAtom0939
    Fin15AnchoredAtom0984 Fin15AnchoredAtom1369 Fin15AnchoredAtom3085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20506
  ] at hbad
  tauto

theorem fin15Anchored_clause21383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0894 Fin15AnchoredAtom3086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24602
  ] at hbad
  tauto

theorem fin15Anchored_clause21384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0895 Fin15AnchoredAtom3086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24602
  ] at hbad
  tauto

theorem fin15Anchored_clause21385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0940 Fin15AnchoredAtom3086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24602
  ] at hbad
  tauto

theorem fin15Anchored_clause21386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0985 Fin15AnchoredAtom3086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24602
  ] at hbad
  tauto

theorem fin15Anchored_clause21387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1370 Fin15AnchoredAtom3086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24602
  ] at hbad
  tauto

theorem fin15Anchored_clause21388 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0894 Fin15AnchoredAtom0895 Fin15AnchoredAtom0940
    Fin15AnchoredAtom0985 Fin15AnchoredAtom1370 Fin15AnchoredAtom3086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24602
  ] at hbad
  tauto

theorem fin15Anchored_clause21389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom3087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00234
  ] at hbad
  tauto

theorem fin15Anchored_clause21390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom3087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00234
  ] at hbad
  tauto

theorem fin15Anchored_clause21391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom3087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00234
  ] at hbad
  tauto

theorem fin15Anchored_clause21392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom3087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00234
  ] at hbad
  tauto

theorem fin15Anchored_clause21393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom3087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00234
  ] at hbad
  tauto

theorem fin15Anchored_clause21394 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom0897 Fin15AnchoredAtom0905
    Fin15AnchoredAtom0986 Fin15AnchoredAtom1371 Fin15AnchoredAtom3087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00234
  ] at hbad
  tauto

theorem fin15Anchored_clause21395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom3088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00362
  ] at hbad
  tauto

theorem fin15Anchored_clause21396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom3088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00362
  ] at hbad
  tauto

theorem fin15Anchored_clause21397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0906 Fin15AnchoredAtom3088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00362
  ] at hbad
  tauto

theorem fin15Anchored_clause21398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom3088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00362
  ] at hbad
  tauto

theorem fin15Anchored_clause21399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3088 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom3088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00362
  ] at hbad
  tauto

theorem fin15Anchored_clause21400 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3088 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom0898 Fin15AnchoredAtom0906
    Fin15AnchoredAtom0987 Fin15AnchoredAtom1372 Fin15AnchoredAtom3088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00362
  ] at hbad
  tauto

theorem fin15Anchored_clause21401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom3089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00618
  ] at hbad
  tauto

theorem fin15Anchored_clause21402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom3089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00618
  ] at hbad
  tauto

theorem fin15Anchored_clause21403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom3089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00618
  ] at hbad
  tauto

theorem fin15Anchored_clause21404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom3089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00618
  ] at hbad
  tauto

theorem fin15Anchored_clause21405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom3089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00618
  ] at hbad
  tauto

theorem fin15Anchored_clause21406 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom0899 Fin15AnchoredAtom0907
    Fin15AnchoredAtom0988 Fin15AnchoredAtom1373 Fin15AnchoredAtom3089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00618
  ] at hbad
  tauto

theorem fin15Anchored_clause21407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom3090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01130
  ] at hbad
  tauto

theorem fin15Anchored_clause21408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom3090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01130
  ] at hbad
  tauto

theorem fin15Anchored_clause21409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom3090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01130
  ] at hbad
  tauto

theorem fin15Anchored_clause21410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom3090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01130
  ] at hbad
  tauto

theorem fin15Anchored_clause21411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom3090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01130
  ] at hbad
  tauto

theorem fin15Anchored_clause21412 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom0900 Fin15AnchoredAtom0908
    Fin15AnchoredAtom0989 Fin15AnchoredAtom1374 Fin15AnchoredAtom3090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01130
  ] at hbad
  tauto

theorem fin15Anchored_clause21413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3091 chi ∧
      ¬Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1375 Fin15AnchoredAtom3091 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02154
  ] at hbad
  tauto

theorem fin15Anchored_clause21414 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3091 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0901 chi ∧
      Fin15AnchoredAtom0909 chi ∧
      Fin15AnchoredAtom0990 chi ∧
      Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom0901 Fin15AnchoredAtom0909
    Fin15AnchoredAtom0990 Fin15AnchoredAtom1375 Fin15AnchoredAtom3091 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02154
  ] at hbad
  tauto

theorem fin15Anchored_clause21415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom3092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04202
  ] at hbad
  tauto

theorem fin15Anchored_clause21416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom3092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04202
  ] at hbad
  tauto

theorem fin15Anchored_clause21417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom3092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04202
  ] at hbad
  tauto

theorem fin15Anchored_clause21418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom3092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04202
  ] at hbad
  tauto

theorem fin15Anchored_clause21419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom3092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04202
  ] at hbad
  tauto

theorem fin15Anchored_clause21420 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom0902 Fin15AnchoredAtom0910
    Fin15AnchoredAtom0991 Fin15AnchoredAtom1376 Fin15AnchoredAtom3092 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04202
  ] at hbad
  tauto

theorem fin15Anchored_clause21421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom3093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08298
  ] at hbad
  tauto

theorem fin15Anchored_clause21422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0903 Fin15AnchoredAtom3093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08298
  ] at hbad
  tauto

theorem fin15Anchored_clause21423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0911 Fin15AnchoredAtom3093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08298
  ] at hbad
  tauto

theorem fin15Anchored_clause21424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0992 Fin15AnchoredAtom3093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08298
  ] at hbad
  tauto

theorem fin15Anchored_clause21425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1377 Fin15AnchoredAtom3093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08298
  ] at hbad
  tauto

theorem fin15Anchored_clause21426 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom0903 Fin15AnchoredAtom0911
    Fin15AnchoredAtom0992 Fin15AnchoredAtom1377 Fin15AnchoredAtom3093 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08298
  ] at hbad
  tauto

theorem fin15Anchored_clause21427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom3094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16490
  ] at hbad
  tauto

theorem fin15Anchored_clause21428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0904 Fin15AnchoredAtom3094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16490
  ] at hbad
  tauto

theorem fin15Anchored_clause21429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0912 Fin15AnchoredAtom3094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16490
  ] at hbad
  tauto

theorem fin15Anchored_clause21430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0993 Fin15AnchoredAtom3094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16490
  ] at hbad
  tauto

theorem fin15Anchored_clause21431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1378 Fin15AnchoredAtom3094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16490
  ] at hbad
  tauto

theorem fin15Anchored_clause21432 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom0904 Fin15AnchoredAtom0912
    Fin15AnchoredAtom0993 Fin15AnchoredAtom1378 Fin15AnchoredAtom3094 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16490
  ] at hbad
  tauto

theorem fin15Anchored_clause21433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom3095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00426
  ] at hbad
  tauto

theorem fin15Anchored_clause21434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom3095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00426
  ] at hbad
  tauto

theorem fin15Anchored_clause21435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom3095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00426
  ] at hbad
  tauto

theorem fin15Anchored_clause21436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3095 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom3095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00426
  ] at hbad
  tauto

theorem fin15Anchored_clause21437 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom0898 Fin15AnchoredAtom0913
    Fin15AnchoredAtom0994 Fin15AnchoredAtom1379 Fin15AnchoredAtom3095 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00426
  ] at hbad
  tauto

theorem fin15Anchored_clause21438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom3096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00682
  ] at hbad
  tauto

theorem fin15Anchored_clause21439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom3096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00682
  ] at hbad
  tauto

theorem fin15Anchored_clause21440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom3096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00682
  ] at hbad
  tauto

theorem fin15Anchored_clause21441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom3096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00682
  ] at hbad
  tauto

theorem fin15Anchored_clause21442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom3096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00682
  ] at hbad
  tauto

theorem fin15Anchored_clause21443 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom0899 Fin15AnchoredAtom0914
    Fin15AnchoredAtom0995 Fin15AnchoredAtom1380 Fin15AnchoredAtom3096 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00682
  ] at hbad
  tauto

theorem fin15Anchored_clause21444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom3097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01194
  ] at hbad
  tauto

theorem fin15Anchored_clause21445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom3097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01194
  ] at hbad
  tauto

theorem fin15Anchored_clause21446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom3097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01194
  ] at hbad
  tauto

theorem fin15Anchored_clause21447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom3097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01194
  ] at hbad
  tauto

theorem fin15Anchored_clause21448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom3097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01194
  ] at hbad
  tauto

theorem fin15Anchored_clause21449 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom0900 Fin15AnchoredAtom0915
    Fin15AnchoredAtom0996 Fin15AnchoredAtom1381 Fin15AnchoredAtom3097 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01194
  ] at hbad
  tauto

theorem fin15Anchored_clause21450 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3098 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom3098 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02218
  ] at hbad
  tauto

theorem fin15Anchored_clause21451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3098 chi ∧
      ¬Fin15AnchoredAtom1382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1382 Fin15AnchoredAtom3098 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02218
  ] at hbad
  tauto

theorem fin15Anchored_clause21452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom3099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04266
  ] at hbad
  tauto

theorem fin15Anchored_clause21453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom3099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04266
  ] at hbad
  tauto

theorem fin15Anchored_clause21454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom3099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04266
  ] at hbad
  tauto

theorem fin15Anchored_clause21455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom3099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04266
  ] at hbad
  tauto

theorem fin15Anchored_clause21456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom3099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04266
  ] at hbad
  tauto

theorem fin15Anchored_clause21457 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom0902 Fin15AnchoredAtom0917
    Fin15AnchoredAtom0998 Fin15AnchoredAtom1383 Fin15AnchoredAtom3099 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04266
  ] at hbad
  tauto

theorem fin15Anchored_clause21458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom3100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08362
  ] at hbad
  tauto

theorem fin15Anchored_clause21459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0903 Fin15AnchoredAtom3100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08362
  ] at hbad
  tauto

theorem fin15Anchored_clause21460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom3100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08362
  ] at hbad
  tauto

theorem fin15Anchored_clause21461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom3100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08362
  ] at hbad
  tauto

theorem fin15Anchored_clause21462 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom3100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08362
  ] at hbad
  tauto

theorem fin15Anchored_clause21463 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom0903 Fin15AnchoredAtom0918
    Fin15AnchoredAtom0999 Fin15AnchoredAtom1384 Fin15AnchoredAtom3100 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08362
  ] at hbad
  tauto

theorem fin15Anchored_clause21464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom3101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16554
  ] at hbad
  tauto

theorem fin15Anchored_clause21465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0904 Fin15AnchoredAtom3101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16554
  ] at hbad
  tauto

theorem fin15Anchored_clause21466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0919 Fin15AnchoredAtom3101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16554
  ] at hbad
  tauto

theorem fin15Anchored_clause21467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1000 Fin15AnchoredAtom3101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16554
  ] at hbad
  tauto

theorem fin15Anchored_clause21468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1385 Fin15AnchoredAtom3101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16554
  ] at hbad
  tauto

theorem fin15Anchored_clause21469 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom0904 Fin15AnchoredAtom0919
    Fin15AnchoredAtom1000 Fin15AnchoredAtom1385 Fin15AnchoredAtom3101 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16554
  ] at hbad
  tauto

theorem fin15Anchored_clause21470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom3102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00810
  ] at hbad
  tauto

theorem fin15Anchored_clause21471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom3102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00810
  ] at hbad
  tauto

theorem fin15Anchored_clause21472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom3102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00810
  ] at hbad
  tauto

theorem fin15Anchored_clause21473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3102 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom3102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00810
  ] at hbad
  tauto

theorem fin15Anchored_clause21474 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom0899 Fin15AnchoredAtom0920
    Fin15AnchoredAtom1001 Fin15AnchoredAtom1386 Fin15AnchoredAtom3102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00810
  ] at hbad
  tauto

theorem fin15Anchored_clause21475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom3103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01322
  ] at hbad
  tauto

theorem fin15Anchored_clause21476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom3103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01322
  ] at hbad
  tauto

theorem fin15Anchored_clause21477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0921 Fin15AnchoredAtom3103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01322
  ] at hbad
  tauto

theorem fin15Anchored_clause21478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1002 Fin15AnchoredAtom3103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01322
  ] at hbad
  tauto

theorem fin15Anchored_clause21479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3103 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom3103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01322
  ] at hbad
  tauto

theorem fin15Anchored_clause21480 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3103 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom0900 Fin15AnchoredAtom0921
    Fin15AnchoredAtom1002 Fin15AnchoredAtom1387 Fin15AnchoredAtom3103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01322
  ] at hbad
  tauto

theorem fin15Anchored_clause21481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom3105 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04394
  ] at hbad
  tauto

theorem fin15Anchored_clause21482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom3105 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04394
  ] at hbad
  tauto

theorem fin15Anchored_clause21483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3105 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1389 Fin15AnchoredAtom3105 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04394
  ] at hbad
  tauto

theorem fin15Anchored_clause21484 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3105 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom0902 Fin15AnchoredAtom0923
    Fin15AnchoredAtom1004 Fin15AnchoredAtom1389 Fin15AnchoredAtom3105 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04394
  ] at hbad
  tauto

theorem fin15Anchored_clause21485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom3106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08490
  ] at hbad
  tauto

theorem fin15Anchored_clause21486 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0903 Fin15AnchoredAtom3106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08490
  ] at hbad
  tauto

theorem fin15Anchored_clause21487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0924 Fin15AnchoredAtom3106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08490
  ] at hbad
  tauto

theorem fin15Anchored_clause21488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1005 Fin15AnchoredAtom3106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08490
  ] at hbad
  tauto

theorem fin15Anchored_clause21489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3106 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1390 Fin15AnchoredAtom3106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08490
  ] at hbad
  tauto

theorem fin15Anchored_clause21490 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom0903 Fin15AnchoredAtom0924
    Fin15AnchoredAtom1005 Fin15AnchoredAtom1390 Fin15AnchoredAtom3106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08490
  ] at hbad
  tauto

theorem fin15Anchored_clause21491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom3107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16682
  ] at hbad
  tauto

theorem fin15Anchored_clause21492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0904 Fin15AnchoredAtom3107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16682
  ] at hbad
  tauto

theorem fin15Anchored_clause21493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1006 Fin15AnchoredAtom3107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16682
  ] at hbad
  tauto

theorem fin15Anchored_clause21494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3107 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1391 Fin15AnchoredAtom3107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16682
  ] at hbad
  tauto

theorem fin15Anchored_clause21495 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3107 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom1006 chi ∧
      Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom0904 Fin15AnchoredAtom0925
    Fin15AnchoredAtom1006 Fin15AnchoredAtom1391 Fin15AnchoredAtom3107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16682
  ] at hbad
  tauto

theorem fin15Anchored_clause21496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom3108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01578
  ] at hbad
  tauto

theorem fin15Anchored_clause21497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom3108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01578
  ] at hbad
  tauto

theorem fin15Anchored_clause21498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom3108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01578
  ] at hbad
  tauto

theorem fin15Anchored_clause21499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom3108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01578
  ] at hbad
  tauto

theorem fin15Anchored_clause21500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom3108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01578
  ] at hbad
  tauto

theorem fin15Anchored_clause21501 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom0900 Fin15AnchoredAtom0926
    Fin15AnchoredAtom1007 Fin15AnchoredAtom1392 Fin15AnchoredAtom3108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01578
  ] at hbad
  tauto

theorem fin15Anchored_clause21502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3109 chi ∧
      ¬Fin15AnchoredAtom0927 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0927 Fin15AnchoredAtom3109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02602
  ] at hbad
  tauto

theorem fin15Anchored_clause21503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3109 chi ∧
      ¬Fin15AnchoredAtom1008 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1008 Fin15AnchoredAtom3109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02602
  ] at hbad
  tauto

end ErdosSzekeres

end
