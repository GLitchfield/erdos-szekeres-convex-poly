module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 127. -/

theorem fin15Anchored_clause16256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0984 Fin15AnchoredAtom1985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20499
  ] at hbad
  tauto

theorem fin15Anchored_clause16257 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1985 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom0488 Fin15AnchoredAtom0532
    Fin15AnchoredAtom0698 Fin15AnchoredAtom0984 Fin15AnchoredAtom1985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20499
  ] at hbad
  tauto

theorem fin15Anchored_clause16258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom1986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24595
  ] at hbad
  tauto

theorem fin15Anchored_clause16259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0488 Fin15AnchoredAtom1986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24595
  ] at hbad
  tauto

theorem fin15Anchored_clause16260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0533 Fin15AnchoredAtom1986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24595
  ] at hbad
  tauto

theorem fin15Anchored_clause16261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0699 Fin15AnchoredAtom1986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24595
  ] at hbad
  tauto

theorem fin15Anchored_clause16262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0985 Fin15AnchoredAtom1986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24595
  ] at hbad
  tauto

theorem fin15Anchored_clause16263 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1986 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom0488 Fin15AnchoredAtom0533
    Fin15AnchoredAtom0699 Fin15AnchoredAtom0985 Fin15AnchoredAtom1986 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24595
  ] at hbad
  tauto

theorem fin15Anchored_clause16264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom1987 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00227
  ] at hbad
  tauto

theorem fin15Anchored_clause16265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom1987 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00227
  ] at hbad
  tauto

theorem fin15Anchored_clause16266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom1987 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00227
  ] at hbad
  tauto

theorem fin15Anchored_clause16267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom1987 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00227
  ] at hbad
  tauto

theorem fin15Anchored_clause16268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom1987 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00227
  ] at hbad
  tauto

theorem fin15Anchored_clause16269 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1987 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom0490 Fin15AnchoredAtom0498
    Fin15AnchoredAtom0700 Fin15AnchoredAtom0986 Fin15AnchoredAtom1987 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00227
  ] at hbad
  tauto

theorem fin15Anchored_clause16270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom1988 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00355
  ] at hbad
  tauto

theorem fin15Anchored_clause16271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom0491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom1988 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00355
  ] at hbad
  tauto

theorem fin15Anchored_clause16272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom0499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom1988 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00355
  ] at hbad
  tauto

theorem fin15Anchored_clause16273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom1988 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00355
  ] at hbad
  tauto

theorem fin15Anchored_clause16274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1988 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom1988 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00355
  ] at hbad
  tauto

theorem fin15Anchored_clause16275 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1988 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom0491 Fin15AnchoredAtom0499
    Fin15AnchoredAtom0701 Fin15AnchoredAtom0987 Fin15AnchoredAtom1988 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00355
  ] at hbad
  tauto

theorem fin15Anchored_clause16276 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom1989 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00611
  ] at hbad
  tauto

theorem fin15Anchored_clause16277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom1989 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00611
  ] at hbad
  tauto

theorem fin15Anchored_clause16278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom1989 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00611
  ] at hbad
  tauto

theorem fin15Anchored_clause16279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom1989 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00611
  ] at hbad
  tauto

theorem fin15Anchored_clause16280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom1989 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00611
  ] at hbad
  tauto

theorem fin15Anchored_clause16281 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1989 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom0492 Fin15AnchoredAtom0500
    Fin15AnchoredAtom0702 Fin15AnchoredAtom0988 Fin15AnchoredAtom1989 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00611
  ] at hbad
  tauto

theorem fin15Anchored_clause16282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom1990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01123
  ] at hbad
  tauto

theorem fin15Anchored_clause16283 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom1990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01123
  ] at hbad
  tauto

theorem fin15Anchored_clause16284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom1990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01123
  ] at hbad
  tauto

theorem fin15Anchored_clause16285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom1990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01123
  ] at hbad
  tauto

theorem fin15Anchored_clause16286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom1990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01123
  ] at hbad
  tauto

theorem fin15Anchored_clause16287 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1990 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom0493 Fin15AnchoredAtom0501
    Fin15AnchoredAtom0703 Fin15AnchoredAtom0989 Fin15AnchoredAtom1990 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01123
  ] at hbad
  tauto

theorem fin15Anchored_clause16288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1991 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom1991 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02147
  ] at hbad
  tauto

theorem fin15Anchored_clause16289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1991 chi ∧
      ¬Fin15AnchoredAtom0502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0502 Fin15AnchoredAtom1991 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02147
  ] at hbad
  tauto

theorem fin15Anchored_clause16290 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1991 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0494 chi ∧
      Fin15AnchoredAtom0502 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0990 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom0494 Fin15AnchoredAtom0502
    Fin15AnchoredAtom0704 Fin15AnchoredAtom0990 Fin15AnchoredAtom1991 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02147
  ] at hbad
  tauto

theorem fin15Anchored_clause16291 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom1992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04195
  ] at hbad
  tauto

theorem fin15Anchored_clause16292 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom1992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04195
  ] at hbad
  tauto

theorem fin15Anchored_clause16293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom1992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04195
  ] at hbad
  tauto

theorem fin15Anchored_clause16294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom1992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04195
  ] at hbad
  tauto

theorem fin15Anchored_clause16295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom1992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04195
  ] at hbad
  tauto

theorem fin15Anchored_clause16296 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1992 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom0495 Fin15AnchoredAtom0503
    Fin15AnchoredAtom0705 Fin15AnchoredAtom0991 Fin15AnchoredAtom1992 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04195
  ] at hbad
  tauto

theorem fin15Anchored_clause16297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom1993 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08291
  ] at hbad
  tauto

theorem fin15Anchored_clause16298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0496 Fin15AnchoredAtom1993 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08291
  ] at hbad
  tauto

theorem fin15Anchored_clause16299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom1993 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08291
  ] at hbad
  tauto

theorem fin15Anchored_clause16300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0706 Fin15AnchoredAtom1993 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08291
  ] at hbad
  tauto

theorem fin15Anchored_clause16301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0992 Fin15AnchoredAtom1993 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08291
  ] at hbad
  tauto

theorem fin15Anchored_clause16302 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1993 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom0496 Fin15AnchoredAtom0504
    Fin15AnchoredAtom0706 Fin15AnchoredAtom0992 Fin15AnchoredAtom1993 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08291
  ] at hbad
  tauto

theorem fin15Anchored_clause16303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom1994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16483
  ] at hbad
  tauto

theorem fin15Anchored_clause16304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0497 Fin15AnchoredAtom1994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16483
  ] at hbad
  tauto

theorem fin15Anchored_clause16305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0505 Fin15AnchoredAtom1994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16483
  ] at hbad
  tauto

theorem fin15Anchored_clause16306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0707 Fin15AnchoredAtom1994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16483
  ] at hbad
  tauto

theorem fin15Anchored_clause16307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0993 Fin15AnchoredAtom1994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16483
  ] at hbad
  tauto

theorem fin15Anchored_clause16308 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1994 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom0497 Fin15AnchoredAtom0505
    Fin15AnchoredAtom0707 Fin15AnchoredAtom0993 Fin15AnchoredAtom1994 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16483
  ] at hbad
  tauto

theorem fin15Anchored_clause16309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom1995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00419
  ] at hbad
  tauto

theorem fin15Anchored_clause16310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom0491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom1995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00419
  ] at hbad
  tauto

theorem fin15Anchored_clause16311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom0506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom1995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00419
  ] at hbad
  tauto

theorem fin15Anchored_clause16312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom1995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00419
  ] at hbad
  tauto

theorem fin15Anchored_clause16313 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1995 chi ∧
      ¬Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom1995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00419
  ] at hbad
  tauto

theorem fin15Anchored_clause16314 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1995 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom0491 Fin15AnchoredAtom0506
    Fin15AnchoredAtom0708 Fin15AnchoredAtom0994 Fin15AnchoredAtom1995 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00419
  ] at hbad
  tauto

theorem fin15Anchored_clause16315 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom1996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00675
  ] at hbad
  tauto

theorem fin15Anchored_clause16316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom1996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00675
  ] at hbad
  tauto

theorem fin15Anchored_clause16317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom1996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00675
  ] at hbad
  tauto

theorem fin15Anchored_clause16318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom1996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00675
  ] at hbad
  tauto

theorem fin15Anchored_clause16319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom1996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00675
  ] at hbad
  tauto

theorem fin15Anchored_clause16320 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1996 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom0492 Fin15AnchoredAtom0507
    Fin15AnchoredAtom0709 Fin15AnchoredAtom0995 Fin15AnchoredAtom1996 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00675
  ] at hbad
  tauto

theorem fin15Anchored_clause16321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom1997 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01187
  ] at hbad
  tauto

theorem fin15Anchored_clause16322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom1997 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01187
  ] at hbad
  tauto

theorem fin15Anchored_clause16323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom1997 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01187
  ] at hbad
  tauto

theorem fin15Anchored_clause16324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom1997 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01187
  ] at hbad
  tauto

theorem fin15Anchored_clause16325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom1997 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01187
  ] at hbad
  tauto

theorem fin15Anchored_clause16326 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1997 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom0493 Fin15AnchoredAtom0508
    Fin15AnchoredAtom0710 Fin15AnchoredAtom0996 Fin15AnchoredAtom1997 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01187
  ] at hbad
  tauto

theorem fin15Anchored_clause16327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1998 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom1998 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02211
  ] at hbad
  tauto

theorem fin15Anchored_clause16328 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom1999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04259
  ] at hbad
  tauto

theorem fin15Anchored_clause16329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom1999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04259
  ] at hbad
  tauto

theorem fin15Anchored_clause16330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom1999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04259
  ] at hbad
  tauto

theorem fin15Anchored_clause16331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom1999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04259
  ] at hbad
  tauto

theorem fin15Anchored_clause16332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom1999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04259
  ] at hbad
  tauto

theorem fin15Anchored_clause16333 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1999 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom0495 Fin15AnchoredAtom0510
    Fin15AnchoredAtom0712 Fin15AnchoredAtom0998 Fin15AnchoredAtom1999 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04259
  ] at hbad
  tauto

theorem fin15Anchored_clause16334 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom2000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08355
  ] at hbad
  tauto

theorem fin15Anchored_clause16335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0496 Fin15AnchoredAtom2000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08355
  ] at hbad
  tauto

theorem fin15Anchored_clause16336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom2000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08355
  ] at hbad
  tauto

theorem fin15Anchored_clause16337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom2000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08355
  ] at hbad
  tauto

theorem fin15Anchored_clause16338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom2000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08355
  ] at hbad
  tauto

theorem fin15Anchored_clause16339 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2000 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom0496 Fin15AnchoredAtom0511
    Fin15AnchoredAtom0713 Fin15AnchoredAtom0999 Fin15AnchoredAtom2000 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08355
  ] at hbad
  tauto

theorem fin15Anchored_clause16340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom2001 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16547
  ] at hbad
  tauto

theorem fin15Anchored_clause16341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0497 Fin15AnchoredAtom2001 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16547
  ] at hbad
  tauto

theorem fin15Anchored_clause16342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0512 Fin15AnchoredAtom2001 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16547
  ] at hbad
  tauto

theorem fin15Anchored_clause16343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0714 Fin15AnchoredAtom2001 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16547
  ] at hbad
  tauto

theorem fin15Anchored_clause16344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1000 Fin15AnchoredAtom2001 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16547
  ] at hbad
  tauto

theorem fin15Anchored_clause16345 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2001 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom0497 Fin15AnchoredAtom0512
    Fin15AnchoredAtom0714 Fin15AnchoredAtom1000 Fin15AnchoredAtom2001 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16547
  ] at hbad
  tauto

theorem fin15Anchored_clause16346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom0491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom2002 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00803
  ] at hbad
  tauto

theorem fin15Anchored_clause16347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom2002 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00803
  ] at hbad
  tauto

theorem fin15Anchored_clause16348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom0513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom2002 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00803
  ] at hbad
  tauto

theorem fin15Anchored_clause16349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom2002 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00803
  ] at hbad
  tauto

theorem fin15Anchored_clause16350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2002 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom2002 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00803
  ] at hbad
  tauto

theorem fin15Anchored_clause16351 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2002 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom0492 Fin15AnchoredAtom0513
    Fin15AnchoredAtom0715 Fin15AnchoredAtom1001 Fin15AnchoredAtom2002 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00803
  ] at hbad
  tauto

theorem fin15Anchored_clause16352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom0491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom2003 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01315
  ] at hbad
  tauto

theorem fin15Anchored_clause16353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom2003 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01315
  ] at hbad
  tauto

theorem fin15Anchored_clause16354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom0514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0514 Fin15AnchoredAtom2003 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01315
  ] at hbad
  tauto

theorem fin15Anchored_clause16355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom0716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom2003 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01315
  ] at hbad
  tauto

theorem fin15Anchored_clause16356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2003 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1002 Fin15AnchoredAtom2003 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01315
  ] at hbad
  tauto

theorem fin15Anchored_clause16357 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2003 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom0493 Fin15AnchoredAtom0514
    Fin15AnchoredAtom0716 Fin15AnchoredAtom1002 Fin15AnchoredAtom2003 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01315
  ] at hbad
  tauto

theorem fin15Anchored_clause16358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom0491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom2005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04387
  ] at hbad
  tauto

theorem fin15Anchored_clause16359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom2005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04387
  ] at hbad
  tauto

theorem fin15Anchored_clause16360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom0516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0516 Fin15AnchoredAtom2005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04387
  ] at hbad
  tauto

theorem fin15Anchored_clause16361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom0718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0718 Fin15AnchoredAtom2005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04387
  ] at hbad
  tauto

theorem fin15Anchored_clause16362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2005 chi ∧
      ¬Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1004 Fin15AnchoredAtom2005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04387
  ] at hbad
  tauto

theorem fin15Anchored_clause16363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2005 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom0495 Fin15AnchoredAtom0516
    Fin15AnchoredAtom0718 Fin15AnchoredAtom1004 Fin15AnchoredAtom2005 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04387
  ] at hbad
  tauto

theorem fin15Anchored_clause16364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom0491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom2006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08483
  ] at hbad
  tauto

theorem fin15Anchored_clause16365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0496 Fin15AnchoredAtom2006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08483
  ] at hbad
  tauto

theorem fin15Anchored_clause16366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom0517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0517 Fin15AnchoredAtom2006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08483
  ] at hbad
  tauto

theorem fin15Anchored_clause16367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom0719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0719 Fin15AnchoredAtom2006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08483
  ] at hbad
  tauto

theorem fin15Anchored_clause16368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2006 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1005 Fin15AnchoredAtom2006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08483
  ] at hbad
  tauto

theorem fin15Anchored_clause16369 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2006 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom0496 Fin15AnchoredAtom0517
    Fin15AnchoredAtom0719 Fin15AnchoredAtom1005 Fin15AnchoredAtom2006 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08483
  ] at hbad
  tauto

theorem fin15Anchored_clause16370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom0491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom2007 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16675
  ] at hbad
  tauto

theorem fin15Anchored_clause16371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2007 chi ∧
      ¬Fin15AnchoredAtom0720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0720 Fin15AnchoredAtom2007 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16675
  ] at hbad
  tauto

theorem fin15Anchored_clause16372 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2007 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom0497 Fin15AnchoredAtom0518
    Fin15AnchoredAtom0720 Fin15AnchoredAtom1006 Fin15AnchoredAtom2007 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16675
  ] at hbad
  tauto

theorem fin15Anchored_clause16373 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom2008 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01571
  ] at hbad
  tauto

theorem fin15Anchored_clause16374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom2008 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01571
  ] at hbad
  tauto

theorem fin15Anchored_clause16375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom2008 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01571
  ] at hbad
  tauto

theorem fin15Anchored_clause16376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom2008 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01571
  ] at hbad
  tauto

theorem fin15Anchored_clause16377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom2008 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01571
  ] at hbad
  tauto

theorem fin15Anchored_clause16378 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2008 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom0493 Fin15AnchoredAtom0519
    Fin15AnchoredAtom0721 Fin15AnchoredAtom1007 Fin15AnchoredAtom2008 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01571
  ] at hbad
  tauto

theorem fin15Anchored_clause16379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2009 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom2009 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02595
  ] at hbad
  tauto

theorem fin15Anchored_clause16380 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom2010 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04643
  ] at hbad
  tauto

theorem fin15Anchored_clause16381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom2010 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04643
  ] at hbad
  tauto

theorem fin15Anchored_clause16382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom2010 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04643
  ] at hbad
  tauto

theorem fin15Anchored_clause16383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom2010 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04643
  ] at hbad
  tauto

end ErdosSzekeres

end
