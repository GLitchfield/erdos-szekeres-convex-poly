module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 061. -/

theorem predecessorHalfFin13_clause18152 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom1167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0061
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18153 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom0351 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0351 PredecessorHalfFin13Atom1167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0061
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18154 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom0387 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom1167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0061
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18155 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom1167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0061
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18156 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1167 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0351 chi ∧
      PredecessorHalfFin13Atom0387 chi ∧
      PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0351
    PredecessorHalfFin13Atom0387 PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom1167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0061
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18157 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom1168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0093
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18158 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom1168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0093
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18159 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom0352 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0352 PredecessorHalfFin13Atom1168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0093
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18160 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom0388 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom1168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0093
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18161 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1168 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom1168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0093
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18162 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1168 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0352 chi ∧
      PredecessorHalfFin13Atom0388 chi ∧
      PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0352
    PredecessorHalfFin13Atom0388 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom1168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0093
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18163 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom1169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18164 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom1169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18165 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom0353 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0353 PredecessorHalfFin13Atom1169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18166 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom0389 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom1169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18167 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1169 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom1169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18168 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1169 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0353 chi ∧
      PredecessorHalfFin13Atom0389 chi ∧
      PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0353
    PredecessorHalfFin13Atom0389 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom1169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0157
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18169 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom1170 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0285
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18170 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom1170 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0285
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18171 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom0354 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0354 PredecessorHalfFin13Atom1170 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0285
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18172 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom0390 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0390 PredecessorHalfFin13Atom1170 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0285
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18173 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1170 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom1170 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0285
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18175 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom1171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0541
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18176 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom1171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0541
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18177 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom0355 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0355 PredecessorHalfFin13Atom1171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0541
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18178 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom0391 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom1171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0541
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18179 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1171 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom1171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0541
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18180 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1171 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0355 chi ∧
      PredecessorHalfFin13Atom0391 chi ∧
      PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0355
    PredecessorHalfFin13Atom0391 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom1171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0541
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18181 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom1172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1053
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18182 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom1172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1053
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18183 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom0356 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0356 PredecessorHalfFin13Atom1172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1053
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18184 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom0392 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom1172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1053
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18185 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1172 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom1172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1053
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18186 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1172 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0356 chi ∧
      PredecessorHalfFin13Atom0392 chi ∧
      PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0356
    PredecessorHalfFin13Atom0392 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom1172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1053
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18193 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom1174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4125
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18194 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom1174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4125
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18195 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom0358 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0358 PredecessorHalfFin13Atom1174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4125
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18196 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom0394 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom1174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4125
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18197 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1174 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom1174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4125
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18198 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1174 chi ∧
      PredecessorHalfFin13Atom0342 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0358 chi ∧
      PredecessorHalfFin13Atom0394 chi ∧
      PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom0358
    PredecessorHalfFin13Atom0394 PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom1174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4125
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18199 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom1175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18200 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom1175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18201 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom0359 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0359 PredecessorHalfFin13Atom1175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18202 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom0395 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom1175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18203 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1175 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom1175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18204 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1175 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0359 chi ∧
      PredecessorHalfFin13Atom0395 chi ∧
      PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0359
    PredecessorHalfFin13Atom0395 PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom1175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0109
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18205 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom1176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18206 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom1176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18207 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom0360 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0360 PredecessorHalfFin13Atom1176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18208 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom0396 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom1176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18209 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1176 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom1176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18210 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1176 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0360 chi ∧
      PredecessorHalfFin13Atom0396 chi ∧
      PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0360
    PredecessorHalfFin13Atom0396 PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom1176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18211 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom1177 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18212 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom1177 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18213 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom0361 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0361 PredecessorHalfFin13Atom1177 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18214 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom0397 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom1177 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18215 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1177 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom1177 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18216 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1177 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0361 chi ∧
      PredecessorHalfFin13Atom0397 chi ∧
      PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0361
    PredecessorHalfFin13Atom0397 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom1177 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0301
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18217 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom1178 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0557
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18218 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom1178 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0557
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18219 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom0362 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0362 PredecessorHalfFin13Atom1178 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0557
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18220 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom0398 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0398 PredecessorHalfFin13Atom1178 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0557
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18221 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1178 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom1178 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0557
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18223 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom1179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1069
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18224 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom1179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1069
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18225 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom0363 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0363 PredecessorHalfFin13Atom1179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1069
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18226 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom0399 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom1179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1069
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18227 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1179 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom1179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1069
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18228 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1179 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0363 chi ∧
      PredecessorHalfFin13Atom0399 chi ∧
      PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0363
    PredecessorHalfFin13Atom0399 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom1179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1069
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18235 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom0343 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom1181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18236 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom1181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18237 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom0365 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0365 PredecessorHalfFin13Atom1181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18238 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom0401 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom1181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18239 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1181 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom1181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18240 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1181 chi ∧
      PredecessorHalfFin13Atom0343 chi ∧
      PredecessorHalfFin13Atom0350 chi ∧
      PredecessorHalfFin13Atom0365 chi ∧
      PredecessorHalfFin13Atom0401 chi ∧
      PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0343 PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom0365
    PredecessorHalfFin13Atom0401 PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom1181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4141
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18241 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom1182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0205
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18242 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom1182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0205
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18243 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom0366 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0366 PredecessorHalfFin13Atom1182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0205
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18244 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom0402 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom1182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0205
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18245 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1182 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom1182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0205
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18246 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1182 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0366 chi ∧
      PredecessorHalfFin13Atom0402 chi ∧
      PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0366
    PredecessorHalfFin13Atom0402 PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom1182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0205
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18247 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom1183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0333
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18248 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom1183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0333
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18249 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom0367 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0367 PredecessorHalfFin13Atom1183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0333
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18250 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom0403 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom1183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0333
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18251 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1183 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom1183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0333
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18252 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1183 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0367 chi ∧
      PredecessorHalfFin13Atom0403 chi ∧
      PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0367
    PredecessorHalfFin13Atom0403 PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom1183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0333
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18253 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom1184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0589
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18254 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom1184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0589
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18255 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom0368 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0368 PredecessorHalfFin13Atom1184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0589
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18256 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom0404 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom1184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0589
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18257 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1184 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom1184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0589
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18258 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1184 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0368 chi ∧
      PredecessorHalfFin13Atom0404 chi ∧
      PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0368
    PredecessorHalfFin13Atom0404 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom1184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0589
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18259 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom1185 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1101
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18260 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom1185 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1101
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18261 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom0369 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0369 PredecessorHalfFin13Atom1185 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1101
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18262 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom0405 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom1185 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1101
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18263 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1185 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom1185 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1101
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18264 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1185 chi ∧
      PredecessorHalfFin13Atom0344 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0369 chi ∧
      PredecessorHalfFin13Atom0405 chi ∧
      PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0369
    PredecessorHalfFin13Atom0405 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom1185 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1101
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18271 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom0344 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0344 PredecessorHalfFin13Atom1187 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18272 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom1187 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18273 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom0371 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0371 PredecessorHalfFin13Atom1187 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18274 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom0407 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0407 PredecessorHalfFin13Atom1187 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18275 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1187 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom1187 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4173
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18277 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom1188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0397
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18278 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom1188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0397
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18279 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom0372 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0372 PredecessorHalfFin13Atom1188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0397
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18280 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom0408 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom1188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0397
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18281 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1188 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom1188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0397
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18282 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1188 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0346 chi ∧
      PredecessorHalfFin13Atom0372 chi ∧
      PredecessorHalfFin13Atom0408 chi ∧
      PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom0372
    PredecessorHalfFin13Atom0408 PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom1188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0397
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18283 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom1189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0653
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18284 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom0347 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom1189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0653
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18285 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom0373 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0373 PredecessorHalfFin13Atom1189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0653
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18286 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom0409 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom1189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0653
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18287 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1189 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom1189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0653
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18288 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1189 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0347 chi ∧
      PredecessorHalfFin13Atom0373 chi ∧
      PredecessorHalfFin13Atom0409 chi ∧
      PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0347 PredecessorHalfFin13Atom0373
    PredecessorHalfFin13Atom0409 PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom1189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0653
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18289 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom1190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1165
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18290 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom0348 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom1190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1165
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18291 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom0374 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0374 PredecessorHalfFin13Atom1190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1165
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18292 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom0410 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom1190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1165
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18293 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1190 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom1190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1165
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18294 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1190 chi ∧
      PredecessorHalfFin13Atom0345 chi ∧
      PredecessorHalfFin13Atom0348 chi ∧
      PredecessorHalfFin13Atom0374 chi ∧
      PredecessorHalfFin13Atom0410 chi ∧
      PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom0348 PredecessorHalfFin13Atom0374
    PredecessorHalfFin13Atom0410 PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom1190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1165
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18301 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom0345 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0345 PredecessorHalfFin13Atom1192 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4237
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18302 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom0350 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0350 PredecessorHalfFin13Atom1192 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4237
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18303 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom0376 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0376 PredecessorHalfFin13Atom1192 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4237
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18304 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom0412 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0412 PredecessorHalfFin13Atom1192 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4237
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18305 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1192 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom1192 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4237
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause18307 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1193 chi ∧
      ¬PredecessorHalfFin13Atom0346 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0346 PredecessorHalfFin13Atom1193 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0781
  ] at hbad
  tauto

end ErdosSzekeres

end
