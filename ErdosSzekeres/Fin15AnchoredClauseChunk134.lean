module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 134. -/

theorem fin15Anchored_clause17152 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom2163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00181
  ] at hbad
  tauto

theorem fin15Anchored_clause17153 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom2163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00181
  ] at hbad
  tauto

theorem fin15Anchored_clause17154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom2163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00181
  ] at hbad
  tauto

theorem fin15Anchored_clause17155 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom0547 Fin15AnchoredAtom0556
    Fin15AnchoredAtom0656 Fin15AnchoredAtom1162 Fin15AnchoredAtom2163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00181
  ] at hbad
  tauto

theorem fin15Anchored_clause17156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2164 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom2164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00309
  ] at hbad
  tauto

theorem fin15Anchored_clause17157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom2165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00565
  ] at hbad
  tauto

theorem fin15Anchored_clause17158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom2165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00565
  ] at hbad
  tauto

theorem fin15Anchored_clause17159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom2165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00565
  ] at hbad
  tauto

theorem fin15Anchored_clause17160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom2165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00565
  ] at hbad
  tauto

theorem fin15Anchored_clause17161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom2165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00565
  ] at hbad
  tauto

theorem fin15Anchored_clause17162 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom0549 Fin15AnchoredAtom0558
    Fin15AnchoredAtom0658 Fin15AnchoredAtom1164 Fin15AnchoredAtom2165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00565
  ] at hbad
  tauto

theorem fin15Anchored_clause17163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom2166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01077
  ] at hbad
  tauto

theorem fin15Anchored_clause17164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom2166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01077
  ] at hbad
  tauto

theorem fin15Anchored_clause17165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom2166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01077
  ] at hbad
  tauto

theorem fin15Anchored_clause17166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom2166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01077
  ] at hbad
  tauto

theorem fin15Anchored_clause17167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom2166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01077
  ] at hbad
  tauto

theorem fin15Anchored_clause17168 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom0550 Fin15AnchoredAtom0559
    Fin15AnchoredAtom0659 Fin15AnchoredAtom1165 Fin15AnchoredAtom2166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01077
  ] at hbad
  tauto

theorem fin15Anchored_clause17169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2167 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom2167 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02101
  ] at hbad
  tauto

theorem fin15Anchored_clause17170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2167 chi ∧
      ¬Fin15AnchoredAtom0660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0660 Fin15AnchoredAtom2167 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02101
  ] at hbad
  tauto

theorem fin15Anchored_clause17171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2167 chi ∧
      ¬Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1166 Fin15AnchoredAtom2167 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02101
  ] at hbad
  tauto

theorem fin15Anchored_clause17172 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2167 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0551 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom0551 Fin15AnchoredAtom0560
    Fin15AnchoredAtom0660 Fin15AnchoredAtom1166 Fin15AnchoredAtom2167 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02101
  ] at hbad
  tauto

theorem fin15Anchored_clause17173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom2168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04149
  ] at hbad
  tauto

theorem fin15Anchored_clause17174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom2168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04149
  ] at hbad
  tauto

theorem fin15Anchored_clause17175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom2168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04149
  ] at hbad
  tauto

theorem fin15Anchored_clause17176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom2168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04149
  ] at hbad
  tauto

theorem fin15Anchored_clause17177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom2168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04149
  ] at hbad
  tauto

theorem fin15Anchored_clause17178 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom0552 Fin15AnchoredAtom0561
    Fin15AnchoredAtom0661 Fin15AnchoredAtom1167 Fin15AnchoredAtom2168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04149
  ] at hbad
  tauto

theorem fin15Anchored_clause17179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom2169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08245
  ] at hbad
  tauto

theorem fin15Anchored_clause17180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0553 Fin15AnchoredAtom2169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08245
  ] at hbad
  tauto

theorem fin15Anchored_clause17181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom2169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08245
  ] at hbad
  tauto

theorem fin15Anchored_clause17182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0662 Fin15AnchoredAtom2169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08245
  ] at hbad
  tauto

theorem fin15Anchored_clause17183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom2169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08245
  ] at hbad
  tauto

theorem fin15Anchored_clause17184 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom0553 Fin15AnchoredAtom0562
    Fin15AnchoredAtom0662 Fin15AnchoredAtom1168 Fin15AnchoredAtom2169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08245
  ] at hbad
  tauto

theorem fin15Anchored_clause17185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom2170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16437
  ] at hbad
  tauto

theorem fin15Anchored_clause17186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0554 Fin15AnchoredAtom2170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16437
  ] at hbad
  tauto

theorem fin15Anchored_clause17187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0563 Fin15AnchoredAtom2170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16437
  ] at hbad
  tauto

theorem fin15Anchored_clause17188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0663 Fin15AnchoredAtom2170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16437
  ] at hbad
  tauto

theorem fin15Anchored_clause17189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1169 Fin15AnchoredAtom2170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16437
  ] at hbad
  tauto

theorem fin15Anchored_clause17190 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom0554 Fin15AnchoredAtom0563
    Fin15AnchoredAtom0663 Fin15AnchoredAtom1169 Fin15AnchoredAtom2170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16437
  ] at hbad
  tauto

theorem fin15Anchored_clause17191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom2171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00213
  ] at hbad
  tauto

theorem fin15Anchored_clause17192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom2171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00213
  ] at hbad
  tauto

theorem fin15Anchored_clause17193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom2171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00213
  ] at hbad
  tauto

theorem fin15Anchored_clause17194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom2171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00213
  ] at hbad
  tauto

theorem fin15Anchored_clause17195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom2171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00213
  ] at hbad
  tauto

theorem fin15Anchored_clause17196 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom0547 Fin15AnchoredAtom0564
    Fin15AnchoredAtom0664 Fin15AnchoredAtom1170 Fin15AnchoredAtom2171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00213
  ] at hbad
  tauto

theorem fin15Anchored_clause17197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2172 chi ∧
      ¬Fin15AnchoredAtom0565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0565 Fin15AnchoredAtom2172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00341
  ] at hbad
  tauto

theorem fin15Anchored_clause17198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2172 chi ∧
      ¬Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom2172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00341
  ] at hbad
  tauto

theorem fin15Anchored_clause17199 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2172 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom1171 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom0548 Fin15AnchoredAtom0565
    Fin15AnchoredAtom0665 Fin15AnchoredAtom1171 Fin15AnchoredAtom2172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00341
  ] at hbad
  tauto

theorem fin15Anchored_clause17200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom2173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00597
  ] at hbad
  tauto

theorem fin15Anchored_clause17201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom2173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00597
  ] at hbad
  tauto

theorem fin15Anchored_clause17202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom2173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00597
  ] at hbad
  tauto

theorem fin15Anchored_clause17203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom2173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00597
  ] at hbad
  tauto

theorem fin15Anchored_clause17204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom2173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00597
  ] at hbad
  tauto

theorem fin15Anchored_clause17205 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom0549 Fin15AnchoredAtom0566
    Fin15AnchoredAtom0666 Fin15AnchoredAtom1172 Fin15AnchoredAtom2173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00597
  ] at hbad
  tauto

theorem fin15Anchored_clause17206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom2174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01109
  ] at hbad
  tauto

theorem fin15Anchored_clause17207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom2174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01109
  ] at hbad
  tauto

theorem fin15Anchored_clause17208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom2174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01109
  ] at hbad
  tauto

theorem fin15Anchored_clause17209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom2174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01109
  ] at hbad
  tauto

theorem fin15Anchored_clause17210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom2174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01109
  ] at hbad
  tauto

theorem fin15Anchored_clause17211 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom0550 Fin15AnchoredAtom0567
    Fin15AnchoredAtom0667 Fin15AnchoredAtom1173 Fin15AnchoredAtom2174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01109
  ] at hbad
  tauto

theorem fin15Anchored_clause17212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2175 chi ∧
      ¬Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom2175 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02133
  ] at hbad
  tauto

theorem fin15Anchored_clause17213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom2176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04181
  ] at hbad
  tauto

theorem fin15Anchored_clause17214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom2176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04181
  ] at hbad
  tauto

theorem fin15Anchored_clause17215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom2176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04181
  ] at hbad
  tauto

theorem fin15Anchored_clause17216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom2176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04181
  ] at hbad
  tauto

theorem fin15Anchored_clause17217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom2176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04181
  ] at hbad
  tauto

theorem fin15Anchored_clause17218 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom0552 Fin15AnchoredAtom0569
    Fin15AnchoredAtom0669 Fin15AnchoredAtom1175 Fin15AnchoredAtom2176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04181
  ] at hbad
  tauto

theorem fin15Anchored_clause17219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom2177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08277
  ] at hbad
  tauto

theorem fin15Anchored_clause17220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0553 Fin15AnchoredAtom2177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08277
  ] at hbad
  tauto

theorem fin15Anchored_clause17221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom2177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08277
  ] at hbad
  tauto

theorem fin15Anchored_clause17222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0670 Fin15AnchoredAtom2177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08277
  ] at hbad
  tauto

theorem fin15Anchored_clause17223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1176 Fin15AnchoredAtom2177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08277
  ] at hbad
  tauto

theorem fin15Anchored_clause17224 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom0553 Fin15AnchoredAtom0570
    Fin15AnchoredAtom0670 Fin15AnchoredAtom1176 Fin15AnchoredAtom2177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08277
  ] at hbad
  tauto

theorem fin15Anchored_clause17225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom2178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16469
  ] at hbad
  tauto

theorem fin15Anchored_clause17226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0554 Fin15AnchoredAtom2178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16469
  ] at hbad
  tauto

theorem fin15Anchored_clause17227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0571 Fin15AnchoredAtom2178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16469
  ] at hbad
  tauto

theorem fin15Anchored_clause17228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0671 Fin15AnchoredAtom2178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16469
  ] at hbad
  tauto

theorem fin15Anchored_clause17229 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1177 Fin15AnchoredAtom2178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16469
  ] at hbad
  tauto

theorem fin15Anchored_clause17230 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom0554 Fin15AnchoredAtom0571
    Fin15AnchoredAtom0671 Fin15AnchoredAtom1177 Fin15AnchoredAtom2178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16469
  ] at hbad
  tauto

theorem fin15Anchored_clause17231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2179 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom2179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00405
  ] at hbad
  tauto

theorem fin15Anchored_clause17232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2179 chi ∧
      ¬Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom2179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00405
  ] at hbad
  tauto

theorem fin15Anchored_clause17233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2179 chi ∧
      ¬Fin15AnchoredAtom1178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1178 Fin15AnchoredAtom2179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00405
  ] at hbad
  tauto

theorem fin15Anchored_clause17234 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2179 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom1178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom0548 Fin15AnchoredAtom0572
    Fin15AnchoredAtom0672 Fin15AnchoredAtom1178 Fin15AnchoredAtom2179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00405
  ] at hbad
  tauto

theorem fin15Anchored_clause17235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom2180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00661
  ] at hbad
  tauto

theorem fin15Anchored_clause17236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom2180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00661
  ] at hbad
  tauto

theorem fin15Anchored_clause17237 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom2180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00661
  ] at hbad
  tauto

theorem fin15Anchored_clause17238 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom2180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00661
  ] at hbad
  tauto

theorem fin15Anchored_clause17239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom2180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00661
  ] at hbad
  tauto

theorem fin15Anchored_clause17240 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom0549 Fin15AnchoredAtom0573
    Fin15AnchoredAtom0673 Fin15AnchoredAtom1179 Fin15AnchoredAtom2180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00661
  ] at hbad
  tauto

theorem fin15Anchored_clause17241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom2181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01173
  ] at hbad
  tauto

theorem fin15Anchored_clause17242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom2181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01173
  ] at hbad
  tauto

theorem fin15Anchored_clause17243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom2181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01173
  ] at hbad
  tauto

theorem fin15Anchored_clause17244 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom2181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01173
  ] at hbad
  tauto

theorem fin15Anchored_clause17245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom2181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01173
  ] at hbad
  tauto

theorem fin15Anchored_clause17246 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom0550 Fin15AnchoredAtom0574
    Fin15AnchoredAtom0674 Fin15AnchoredAtom1180 Fin15AnchoredAtom2181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01173
  ] at hbad
  tauto

theorem fin15Anchored_clause17247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2182 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom2182 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02197
  ] at hbad
  tauto

theorem fin15Anchored_clause17248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2182 chi ∧
      ¬Fin15AnchoredAtom0675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0675 Fin15AnchoredAtom2182 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02197
  ] at hbad
  tauto

theorem fin15Anchored_clause17249 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2182 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0551 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom1181 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom0551 Fin15AnchoredAtom0575
    Fin15AnchoredAtom0675 Fin15AnchoredAtom1181 Fin15AnchoredAtom2182 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02197
  ] at hbad
  tauto

theorem fin15Anchored_clause17250 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom2183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04245
  ] at hbad
  tauto

theorem fin15Anchored_clause17251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom2183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04245
  ] at hbad
  tauto

theorem fin15Anchored_clause17252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom2183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04245
  ] at hbad
  tauto

theorem fin15Anchored_clause17253 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom2183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04245
  ] at hbad
  tauto

theorem fin15Anchored_clause17254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom2183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04245
  ] at hbad
  tauto

theorem fin15Anchored_clause17255 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom0552 Fin15AnchoredAtom0576
    Fin15AnchoredAtom0676 Fin15AnchoredAtom1182 Fin15AnchoredAtom2183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04245
  ] at hbad
  tauto

theorem fin15Anchored_clause17256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom2184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08341
  ] at hbad
  tauto

theorem fin15Anchored_clause17257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0553 Fin15AnchoredAtom2184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08341
  ] at hbad
  tauto

theorem fin15Anchored_clause17258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom2184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08341
  ] at hbad
  tauto

theorem fin15Anchored_clause17259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0677 Fin15AnchoredAtom2184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08341
  ] at hbad
  tauto

theorem fin15Anchored_clause17260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1183 Fin15AnchoredAtom2184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08341
  ] at hbad
  tauto

theorem fin15Anchored_clause17261 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom0553 Fin15AnchoredAtom0577
    Fin15AnchoredAtom0677 Fin15AnchoredAtom1183 Fin15AnchoredAtom2184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08341
  ] at hbad
  tauto

theorem fin15Anchored_clause17262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom2185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16533
  ] at hbad
  tauto

theorem fin15Anchored_clause17263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0554 Fin15AnchoredAtom2185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16533
  ] at hbad
  tauto

theorem fin15Anchored_clause17264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0578 Fin15AnchoredAtom2185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16533
  ] at hbad
  tauto

theorem fin15Anchored_clause17265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0678 Fin15AnchoredAtom2185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16533
  ] at hbad
  tauto

theorem fin15Anchored_clause17266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1184 Fin15AnchoredAtom2185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16533
  ] at hbad
  tauto

theorem fin15Anchored_clause17267 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom0547 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom0554 Fin15AnchoredAtom0578
    Fin15AnchoredAtom0678 Fin15AnchoredAtom1184 Fin15AnchoredAtom2185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16533
  ] at hbad
  tauto

theorem fin15Anchored_clause17268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2186 chi ∧
      ¬Fin15AnchoredAtom0549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0549 Fin15AnchoredAtom2186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00789
  ] at hbad
  tauto

theorem fin15Anchored_clause17269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2186 chi ∧
      ¬Fin15AnchoredAtom0579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0579 Fin15AnchoredAtom2186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00789
  ] at hbad
  tauto

theorem fin15Anchored_clause17270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2186 chi ∧
      ¬Fin15AnchoredAtom1185 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1185 Fin15AnchoredAtom2186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00789
  ] at hbad
  tauto

theorem fin15Anchored_clause17271 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2186 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0549 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom1185 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0548 Fin15AnchoredAtom0549 Fin15AnchoredAtom0579
    Fin15AnchoredAtom0679 Fin15AnchoredAtom1185 Fin15AnchoredAtom2186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00789
  ] at hbad
  tauto

theorem fin15Anchored_clause17272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2187 chi ∧
      ¬Fin15AnchoredAtom0550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0550 Fin15AnchoredAtom2187 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01301
  ] at hbad
  tauto

theorem fin15Anchored_clause17273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2187 chi ∧
      ¬Fin15AnchoredAtom1186 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1186 Fin15AnchoredAtom2187 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01301
  ] at hbad
  tauto

theorem fin15Anchored_clause17274 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2187 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0550 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom1186 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0548 Fin15AnchoredAtom0550 Fin15AnchoredAtom0580
    Fin15AnchoredAtom0680 Fin15AnchoredAtom1186 Fin15AnchoredAtom2187 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01301
  ] at hbad
  tauto

theorem fin15Anchored_clause17275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2189 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom2189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04373
  ] at hbad
  tauto

theorem fin15Anchored_clause17276 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2189 chi ∧
      Fin15AnchoredAtom0548 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0582 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom1188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0548 Fin15AnchoredAtom0552 Fin15AnchoredAtom0582
    Fin15AnchoredAtom0682 Fin15AnchoredAtom1188 Fin15AnchoredAtom2189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04373
  ] at hbad
  tauto

theorem fin15Anchored_clause17277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2190 chi ∧
      ¬Fin15AnchoredAtom0583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0583 Fin15AnchoredAtom2190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08469
  ] at hbad
  tauto

theorem fin15Anchored_clause17278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2191 chi ∧
      ¬Fin15AnchoredAtom0548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0548 Fin15AnchoredAtom2191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16661
  ] at hbad
  tauto

theorem fin15Anchored_clause17279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2191 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0554 Fin15AnchoredAtom2191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16661
  ] at hbad
  tauto

end ErdosSzekeres

end
