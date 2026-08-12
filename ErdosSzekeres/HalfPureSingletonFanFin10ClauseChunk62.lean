module

public import ErdosSzekeres.HalfPureSingletonFanFin10Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic clauses for retained Fin10 LRAT leaf chunk 62. -/

theorem halfPureSingletonFanFin10_clause12683 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0150 χ ∧
      HalfPureSingletonFanFin10Atom0151 χ ∧
      HalfPureSingletonFanFin10Atom0154 χ ∧
      HalfPureSingletonFanFin10Atom0160 χ ∧
      HalfPureSingletonFanFin10Atom0163 χ ∧
      HalfPureSingletonFanFin10Atom0166 χ ∧
      HalfPureSingletonFanFin10Atom0175 χ ∧
      HalfPureSingletonFanFin10Atom0178 χ ∧
      HalfPureSingletonFanFin10Atom0181 χ ∧
      HalfPureSingletonFanFin10Atom0197 χ ∧
      HalfPureSingletonFanFin10Atom0266 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ ∧
      HalfPureSingletonFanFin10Atom0288 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 3, 5, 6, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 6, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0150 HalfPureSingletonFanFin10Atom0151
    HalfPureSingletonFanFin10Atom0154 HalfPureSingletonFanFin10Atom0160
    HalfPureSingletonFanFin10Atom0163 HalfPureSingletonFanFin10Atom0166
    HalfPureSingletonFanFin10Atom0175 HalfPureSingletonFanFin10Atom0178
    HalfPureSingletonFanFin10Atom0181 HalfPureSingletonFanFin10Atom0197
    HalfPureSingletonFanFin10Atom0266 HalfPureSingletonFanFin10Atom0269
    HalfPureSingletonFanFin10Atom0272 HalfPureSingletonFanFin10Atom0288
    HalfPureSingletonFanFin10Atom0308 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12684 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0150 χ ∧
      HalfPureSingletonFanFin10Atom0152 χ ∧
      HalfPureSingletonFanFin10Atom0153 χ ∧
      HalfPureSingletonFanFin10Atom0161 χ ∧
      HalfPureSingletonFanFin10Atom0162 χ ∧
      HalfPureSingletonFanFin10Atom0167 χ ∧
      HalfPureSingletonFanFin10Atom0176 χ ∧
      HalfPureSingletonFanFin10Atom0177 χ ∧
      HalfPureSingletonFanFin10Atom0182 χ ∧
      HalfPureSingletonFanFin10Atom0198 χ ∧
      HalfPureSingletonFanFin10Atom0267 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ ∧
      HalfPureSingletonFanFin10Atom0273 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ ∧
      HalfPureSingletonFanFin10Atom0309 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 3, 5, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0150 HalfPureSingletonFanFin10Atom0152
    HalfPureSingletonFanFin10Atom0153 HalfPureSingletonFanFin10Atom0161
    HalfPureSingletonFanFin10Atom0162 HalfPureSingletonFanFin10Atom0167
    HalfPureSingletonFanFin10Atom0176 HalfPureSingletonFanFin10Atom0177
    HalfPureSingletonFanFin10Atom0182 HalfPureSingletonFanFin10Atom0198
    HalfPureSingletonFanFin10Atom0267 HalfPureSingletonFanFin10Atom0268
    HalfPureSingletonFanFin10Atom0273 HalfPureSingletonFanFin10Atom0289
    HalfPureSingletonFanFin10Atom0309 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12685 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0150 χ ∧
      HalfPureSingletonFanFin10Atom0152 χ ∧
      HalfPureSingletonFanFin10Atom0154 χ ∧
      HalfPureSingletonFanFin10Atom0161 χ ∧
      HalfPureSingletonFanFin10Atom0163 χ ∧
      HalfPureSingletonFanFin10Atom0168 χ ∧
      HalfPureSingletonFanFin10Atom0176 χ ∧
      HalfPureSingletonFanFin10Atom0178 χ ∧
      HalfPureSingletonFanFin10Atom0183 χ ∧
      HalfPureSingletonFanFin10Atom0199 χ ∧
      HalfPureSingletonFanFin10Atom0267 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ ∧
      HalfPureSingletonFanFin10Atom0274 χ ∧
      HalfPureSingletonFanFin10Atom0290 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 3, 5, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0150 HalfPureSingletonFanFin10Atom0152
    HalfPureSingletonFanFin10Atom0154 HalfPureSingletonFanFin10Atom0161
    HalfPureSingletonFanFin10Atom0163 HalfPureSingletonFanFin10Atom0168
    HalfPureSingletonFanFin10Atom0176 HalfPureSingletonFanFin10Atom0178
    HalfPureSingletonFanFin10Atom0183 HalfPureSingletonFanFin10Atom0199
    HalfPureSingletonFanFin10Atom0267 HalfPureSingletonFanFin10Atom0269
    HalfPureSingletonFanFin10Atom0274 HalfPureSingletonFanFin10Atom0290
    HalfPureSingletonFanFin10Atom0310 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12686 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0150 χ ∧
      HalfPureSingletonFanFin10Atom0153 χ ∧
      HalfPureSingletonFanFin10Atom0154 χ ∧
      HalfPureSingletonFanFin10Atom0162 χ ∧
      HalfPureSingletonFanFin10Atom0163 χ ∧
      HalfPureSingletonFanFin10Atom0169 χ ∧
      HalfPureSingletonFanFin10Atom0177 χ ∧
      HalfPureSingletonFanFin10Atom0178 χ ∧
      HalfPureSingletonFanFin10Atom0184 χ ∧
      HalfPureSingletonFanFin10Atom0200 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ ∧
      HalfPureSingletonFanFin10Atom0311 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 3, 5, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 5, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0150 HalfPureSingletonFanFin10Atom0153
    HalfPureSingletonFanFin10Atom0154 HalfPureSingletonFanFin10Atom0162
    HalfPureSingletonFanFin10Atom0163 HalfPureSingletonFanFin10Atom0169
    HalfPureSingletonFanFin10Atom0177 HalfPureSingletonFanFin10Atom0178
    HalfPureSingletonFanFin10Atom0184 HalfPureSingletonFanFin10Atom0200
    HalfPureSingletonFanFin10Atom0268 HalfPureSingletonFanFin10Atom0269
    HalfPureSingletonFanFin10Atom0275 HalfPureSingletonFanFin10Atom0291
    HalfPureSingletonFanFin10Atom0311 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12687 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0151 χ ∧
      HalfPureSingletonFanFin10Atom0152 χ ∧
      HalfPureSingletonFanFin10Atom0153 χ ∧
      HalfPureSingletonFanFin10Atom0164 χ ∧
      HalfPureSingletonFanFin10Atom0165 χ ∧
      HalfPureSingletonFanFin10Atom0167 χ ∧
      HalfPureSingletonFanFin10Atom0179 χ ∧
      HalfPureSingletonFanFin10Atom0180 χ ∧
      HalfPureSingletonFanFin10Atom0182 χ ∧
      HalfPureSingletonFanFin10Atom0201 χ ∧
      HalfPureSingletonFanFin10Atom0270 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ ∧
      HalfPureSingletonFanFin10Atom0273 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 3, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0151 HalfPureSingletonFanFin10Atom0152
    HalfPureSingletonFanFin10Atom0153 HalfPureSingletonFanFin10Atom0164
    HalfPureSingletonFanFin10Atom0165 HalfPureSingletonFanFin10Atom0167
    HalfPureSingletonFanFin10Atom0179 HalfPureSingletonFanFin10Atom0180
    HalfPureSingletonFanFin10Atom0182 HalfPureSingletonFanFin10Atom0201
    HalfPureSingletonFanFin10Atom0270 HalfPureSingletonFanFin10Atom0271
    HalfPureSingletonFanFin10Atom0273 HalfPureSingletonFanFin10Atom0292
    HalfPureSingletonFanFin10Atom0312 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12688 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0151 χ ∧
      HalfPureSingletonFanFin10Atom0152 χ ∧
      HalfPureSingletonFanFin10Atom0154 χ ∧
      HalfPureSingletonFanFin10Atom0164 χ ∧
      HalfPureSingletonFanFin10Atom0166 χ ∧
      HalfPureSingletonFanFin10Atom0168 χ ∧
      HalfPureSingletonFanFin10Atom0179 χ ∧
      HalfPureSingletonFanFin10Atom0181 χ ∧
      HalfPureSingletonFanFin10Atom0183 χ ∧
      HalfPureSingletonFanFin10Atom0202 χ ∧
      HalfPureSingletonFanFin10Atom0270 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ ∧
      HalfPureSingletonFanFin10Atom0274 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 3, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0151 HalfPureSingletonFanFin10Atom0152
    HalfPureSingletonFanFin10Atom0154 HalfPureSingletonFanFin10Atom0164
    HalfPureSingletonFanFin10Atom0166 HalfPureSingletonFanFin10Atom0168
    HalfPureSingletonFanFin10Atom0179 HalfPureSingletonFanFin10Atom0181
    HalfPureSingletonFanFin10Atom0183 HalfPureSingletonFanFin10Atom0202
    HalfPureSingletonFanFin10Atom0270 HalfPureSingletonFanFin10Atom0272
    HalfPureSingletonFanFin10Atom0274 HalfPureSingletonFanFin10Atom0293
    HalfPureSingletonFanFin10Atom0313 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12689 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0151 χ ∧
      HalfPureSingletonFanFin10Atom0153 χ ∧
      HalfPureSingletonFanFin10Atom0154 χ ∧
      HalfPureSingletonFanFin10Atom0165 χ ∧
      HalfPureSingletonFanFin10Atom0166 χ ∧
      HalfPureSingletonFanFin10Atom0169 χ ∧
      HalfPureSingletonFanFin10Atom0180 χ ∧
      HalfPureSingletonFanFin10Atom0181 χ ∧
      HalfPureSingletonFanFin10Atom0184 χ ∧
      HalfPureSingletonFanFin10Atom0203 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 3, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0151 HalfPureSingletonFanFin10Atom0153
    HalfPureSingletonFanFin10Atom0154 HalfPureSingletonFanFin10Atom0165
    HalfPureSingletonFanFin10Atom0166 HalfPureSingletonFanFin10Atom0169
    HalfPureSingletonFanFin10Atom0180 HalfPureSingletonFanFin10Atom0181
    HalfPureSingletonFanFin10Atom0184 HalfPureSingletonFanFin10Atom0203
    HalfPureSingletonFanFin10Atom0271 HalfPureSingletonFanFin10Atom0272
    HalfPureSingletonFanFin10Atom0275 HalfPureSingletonFanFin10Atom0294
    HalfPureSingletonFanFin10Atom0314 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12690 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0152 χ ∧
      HalfPureSingletonFanFin10Atom0153 χ ∧
      HalfPureSingletonFanFin10Atom0154 χ ∧
      HalfPureSingletonFanFin10Atom0167 χ ∧
      HalfPureSingletonFanFin10Atom0168 χ ∧
      HalfPureSingletonFanFin10Atom0169 χ ∧
      HalfPureSingletonFanFin10Atom0182 χ ∧
      HalfPureSingletonFanFin10Atom0183 χ ∧
      HalfPureSingletonFanFin10Atom0184 χ ∧
      HalfPureSingletonFanFin10Atom0204 χ ∧
      HalfPureSingletonFanFin10Atom0273 χ ∧
      HalfPureSingletonFanFin10Atom0274 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 3, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 3, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0152 HalfPureSingletonFanFin10Atom0153
    HalfPureSingletonFanFin10Atom0154 HalfPureSingletonFanFin10Atom0167
    HalfPureSingletonFanFin10Atom0168 HalfPureSingletonFanFin10Atom0169
    HalfPureSingletonFanFin10Atom0182 HalfPureSingletonFanFin10Atom0183
    HalfPureSingletonFanFin10Atom0184 HalfPureSingletonFanFin10Atom0204
    HalfPureSingletonFanFin10Atom0273 HalfPureSingletonFanFin10Atom0274
    HalfPureSingletonFanFin10Atom0275 HalfPureSingletonFanFin10Atom0295
    HalfPureSingletonFanFin10Atom0315 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12701 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0160 χ ∧
      HalfPureSingletonFanFin10Atom0161 χ ∧
      HalfPureSingletonFanFin10Atom0162 χ ∧
      HalfPureSingletonFanFin10Atom0164 χ ∧
      HalfPureSingletonFanFin10Atom0165 χ ∧
      HalfPureSingletonFanFin10Atom0167 χ ∧
      HalfPureSingletonFanFin10Atom0195 χ ∧
      HalfPureSingletonFanFin10Atom0196 χ ∧
      HalfPureSingletonFanFin10Atom0198 χ ∧
      HalfPureSingletonFanFin10Atom0201 χ ∧
      HalfPureSingletonFanFin10Atom0286 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ ∧
      HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 5, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0160 HalfPureSingletonFanFin10Atom0161
    HalfPureSingletonFanFin10Atom0162 HalfPureSingletonFanFin10Atom0164
    HalfPureSingletonFanFin10Atom0165 HalfPureSingletonFanFin10Atom0167
    HalfPureSingletonFanFin10Atom0195 HalfPureSingletonFanFin10Atom0196
    HalfPureSingletonFanFin10Atom0198 HalfPureSingletonFanFin10Atom0201
    HalfPureSingletonFanFin10Atom0286 HalfPureSingletonFanFin10Atom0287
    HalfPureSingletonFanFin10Atom0289 HalfPureSingletonFanFin10Atom0292
    HalfPureSingletonFanFin10Atom0326 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12702 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0160 χ ∧
      HalfPureSingletonFanFin10Atom0161 χ ∧
      HalfPureSingletonFanFin10Atom0163 χ ∧
      HalfPureSingletonFanFin10Atom0164 χ ∧
      HalfPureSingletonFanFin10Atom0166 χ ∧
      HalfPureSingletonFanFin10Atom0168 χ ∧
      HalfPureSingletonFanFin10Atom0195 χ ∧
      HalfPureSingletonFanFin10Atom0197 χ ∧
      HalfPureSingletonFanFin10Atom0199 χ ∧
      HalfPureSingletonFanFin10Atom0202 χ ∧
      HalfPureSingletonFanFin10Atom0286 χ ∧
      HalfPureSingletonFanFin10Atom0288 χ ∧
      HalfPureSingletonFanFin10Atom0290 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ ∧
      HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 5, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0160 HalfPureSingletonFanFin10Atom0161
    HalfPureSingletonFanFin10Atom0163 HalfPureSingletonFanFin10Atom0164
    HalfPureSingletonFanFin10Atom0166 HalfPureSingletonFanFin10Atom0168
    HalfPureSingletonFanFin10Atom0195 HalfPureSingletonFanFin10Atom0197
    HalfPureSingletonFanFin10Atom0199 HalfPureSingletonFanFin10Atom0202
    HalfPureSingletonFanFin10Atom0286 HalfPureSingletonFanFin10Atom0288
    HalfPureSingletonFanFin10Atom0290 HalfPureSingletonFanFin10Atom0293
    HalfPureSingletonFanFin10Atom0327 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12703 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0160 χ ∧
      HalfPureSingletonFanFin10Atom0162 χ ∧
      HalfPureSingletonFanFin10Atom0163 χ ∧
      HalfPureSingletonFanFin10Atom0165 χ ∧
      HalfPureSingletonFanFin10Atom0166 χ ∧
      HalfPureSingletonFanFin10Atom0169 χ ∧
      HalfPureSingletonFanFin10Atom0196 χ ∧
      HalfPureSingletonFanFin10Atom0197 χ ∧
      HalfPureSingletonFanFin10Atom0200 χ ∧
      HalfPureSingletonFanFin10Atom0203 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ ∧
      HalfPureSingletonFanFin10Atom0288 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ ∧
      HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 5, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0160 HalfPureSingletonFanFin10Atom0162
    HalfPureSingletonFanFin10Atom0163 HalfPureSingletonFanFin10Atom0165
    HalfPureSingletonFanFin10Atom0166 HalfPureSingletonFanFin10Atom0169
    HalfPureSingletonFanFin10Atom0196 HalfPureSingletonFanFin10Atom0197
    HalfPureSingletonFanFin10Atom0200 HalfPureSingletonFanFin10Atom0203
    HalfPureSingletonFanFin10Atom0287 HalfPureSingletonFanFin10Atom0288
    HalfPureSingletonFanFin10Atom0291 HalfPureSingletonFanFin10Atom0294
    HalfPureSingletonFanFin10Atom0328 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12704 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0161 χ ∧
      HalfPureSingletonFanFin10Atom0162 χ ∧
      HalfPureSingletonFanFin10Atom0163 χ ∧
      HalfPureSingletonFanFin10Atom0167 χ ∧
      HalfPureSingletonFanFin10Atom0168 χ ∧
      HalfPureSingletonFanFin10Atom0169 χ ∧
      HalfPureSingletonFanFin10Atom0198 χ ∧
      HalfPureSingletonFanFin10Atom0199 χ ∧
      HalfPureSingletonFanFin10Atom0200 χ ∧
      HalfPureSingletonFanFin10Atom0204 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ ∧
      HalfPureSingletonFanFin10Atom0290 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ ∧
      HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 5, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 5, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0161 HalfPureSingletonFanFin10Atom0162
    HalfPureSingletonFanFin10Atom0163 HalfPureSingletonFanFin10Atom0167
    HalfPureSingletonFanFin10Atom0168 HalfPureSingletonFanFin10Atom0169
    HalfPureSingletonFanFin10Atom0198 HalfPureSingletonFanFin10Atom0199
    HalfPureSingletonFanFin10Atom0200 HalfPureSingletonFanFin10Atom0204
    HalfPureSingletonFanFin10Atom0289 HalfPureSingletonFanFin10Atom0290
    HalfPureSingletonFanFin10Atom0291 HalfPureSingletonFanFin10Atom0295
    HalfPureSingletonFanFin10Atom0329 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12705 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0164 χ ∧
      HalfPureSingletonFanFin10Atom0165 χ ∧
      HalfPureSingletonFanFin10Atom0166 χ ∧
      HalfPureSingletonFanFin10Atom0167 χ ∧
      HalfPureSingletonFanFin10Atom0168 χ ∧
      HalfPureSingletonFanFin10Atom0169 χ ∧
      HalfPureSingletonFanFin10Atom0201 χ ∧
      HalfPureSingletonFanFin10Atom0202 χ ∧
      HalfPureSingletonFanFin10Atom0203 χ ∧
      HalfPureSingletonFanFin10Atom0204 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ ∧
      HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 2, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 2, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0164 HalfPureSingletonFanFin10Atom0165
    HalfPureSingletonFanFin10Atom0166 HalfPureSingletonFanFin10Atom0167
    HalfPureSingletonFanFin10Atom0168 HalfPureSingletonFanFin10Atom0169
    HalfPureSingletonFanFin10Atom0201 HalfPureSingletonFanFin10Atom0202
    HalfPureSingletonFanFin10Atom0203 HalfPureSingletonFanFin10Atom0204
    HalfPureSingletonFanFin10Atom0292 HalfPureSingletonFanFin10Atom0293
    HalfPureSingletonFanFin10Atom0294 HalfPureSingletonFanFin10Atom0295
    HalfPureSingletonFanFin10Atom0330 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12716 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0175 χ ∧
      HalfPureSingletonFanFin10Atom0176 χ ∧
      HalfPureSingletonFanFin10Atom0177 χ ∧
      HalfPureSingletonFanFin10Atom0179 χ ∧
      HalfPureSingletonFanFin10Atom0180 χ ∧
      HalfPureSingletonFanFin10Atom0182 χ ∧
      HalfPureSingletonFanFin10Atom0195 χ ∧
      HalfPureSingletonFanFin10Atom0196 χ ∧
      HalfPureSingletonFanFin10Atom0198 χ ∧
      HalfPureSingletonFanFin10Atom0201 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ ∧
      HalfPureSingletonFanFin10Atom0309 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ ∧
      HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 3, 5, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0175 HalfPureSingletonFanFin10Atom0176
    HalfPureSingletonFanFin10Atom0177 HalfPureSingletonFanFin10Atom0179
    HalfPureSingletonFanFin10Atom0180 HalfPureSingletonFanFin10Atom0182
    HalfPureSingletonFanFin10Atom0195 HalfPureSingletonFanFin10Atom0196
    HalfPureSingletonFanFin10Atom0198 HalfPureSingletonFanFin10Atom0201
    HalfPureSingletonFanFin10Atom0306 HalfPureSingletonFanFin10Atom0307
    HalfPureSingletonFanFin10Atom0309 HalfPureSingletonFanFin10Atom0312
    HalfPureSingletonFanFin10Atom0326 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12717 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0175 χ ∧
      HalfPureSingletonFanFin10Atom0176 χ ∧
      HalfPureSingletonFanFin10Atom0178 χ ∧
      HalfPureSingletonFanFin10Atom0179 χ ∧
      HalfPureSingletonFanFin10Atom0181 χ ∧
      HalfPureSingletonFanFin10Atom0183 χ ∧
      HalfPureSingletonFanFin10Atom0195 χ ∧
      HalfPureSingletonFanFin10Atom0197 χ ∧
      HalfPureSingletonFanFin10Atom0199 χ ∧
      HalfPureSingletonFanFin10Atom0202 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ ∧
      HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 3, 5, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0175 HalfPureSingletonFanFin10Atom0176
    HalfPureSingletonFanFin10Atom0178 HalfPureSingletonFanFin10Atom0179
    HalfPureSingletonFanFin10Atom0181 HalfPureSingletonFanFin10Atom0183
    HalfPureSingletonFanFin10Atom0195 HalfPureSingletonFanFin10Atom0197
    HalfPureSingletonFanFin10Atom0199 HalfPureSingletonFanFin10Atom0202
    HalfPureSingletonFanFin10Atom0306 HalfPureSingletonFanFin10Atom0308
    HalfPureSingletonFanFin10Atom0310 HalfPureSingletonFanFin10Atom0313
    HalfPureSingletonFanFin10Atom0327 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12718 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0175 χ ∧
      HalfPureSingletonFanFin10Atom0177 χ ∧
      HalfPureSingletonFanFin10Atom0178 χ ∧
      HalfPureSingletonFanFin10Atom0180 χ ∧
      HalfPureSingletonFanFin10Atom0181 χ ∧
      HalfPureSingletonFanFin10Atom0184 χ ∧
      HalfPureSingletonFanFin10Atom0196 χ ∧
      HalfPureSingletonFanFin10Atom0197 χ ∧
      HalfPureSingletonFanFin10Atom0200 χ ∧
      HalfPureSingletonFanFin10Atom0203 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ ∧
      HalfPureSingletonFanFin10Atom0311 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ ∧
      HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {0, 3, 5, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{0, 3, 5, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0175 HalfPureSingletonFanFin10Atom0177
    HalfPureSingletonFanFin10Atom0178 HalfPureSingletonFanFin10Atom0180
    HalfPureSingletonFanFin10Atom0181 HalfPureSingletonFanFin10Atom0184
    HalfPureSingletonFanFin10Atom0196 HalfPureSingletonFanFin10Atom0197
    HalfPureSingletonFanFin10Atom0200 HalfPureSingletonFanFin10Atom0203
    HalfPureSingletonFanFin10Atom0307 HalfPureSingletonFanFin10Atom0308
    HalfPureSingletonFanFin10Atom0311 HalfPureSingletonFanFin10Atom0314
    HalfPureSingletonFanFin10Atom0328 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12784 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0261 χ ∧
      HalfPureSingletonFanFin10Atom0262 χ ∧
      HalfPureSingletonFanFin10Atom0264 χ ∧
      HalfPureSingletonFanFin10Atom0266 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ ∧
      HalfPureSingletonFanFin10Atom0276 χ ∧
      HalfPureSingletonFanFin10Atom0278 χ ∧
      HalfPureSingletonFanFin10Atom0281 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ ∧
      HalfPureSingletonFanFin10Atom0296 χ ∧
      HalfPureSingletonFanFin10Atom0298 χ ∧
      HalfPureSingletonFanFin10Atom0301 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ ∧
      HalfPureSingletonFanFin10Atom0317 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 4, 5, 6, 8} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 6, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0261 HalfPureSingletonFanFin10Atom0262
    HalfPureSingletonFanFin10Atom0264 HalfPureSingletonFanFin10Atom0266
    HalfPureSingletonFanFin10Atom0268 HalfPureSingletonFanFin10Atom0271
    HalfPureSingletonFanFin10Atom0276 HalfPureSingletonFanFin10Atom0278
    HalfPureSingletonFanFin10Atom0281 HalfPureSingletonFanFin10Atom0287
    HalfPureSingletonFanFin10Atom0296 HalfPureSingletonFanFin10Atom0298
    HalfPureSingletonFanFin10Atom0301 HalfPureSingletonFanFin10Atom0307
    HalfPureSingletonFanFin10Atom0317 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12786 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0261 χ ∧
      HalfPureSingletonFanFin10Atom0263 χ ∧
      HalfPureSingletonFanFin10Atom0264 χ ∧
      HalfPureSingletonFanFin10Atom0267 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ ∧
      HalfPureSingletonFanFin10Atom0273 χ ∧
      HalfPureSingletonFanFin10Atom0277 χ ∧
      HalfPureSingletonFanFin10Atom0278 χ ∧
      HalfPureSingletonFanFin10Atom0283 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ ∧
      HalfPureSingletonFanFin10Atom0297 χ ∧
      HalfPureSingletonFanFin10Atom0298 χ ∧
      HalfPureSingletonFanFin10Atom0303 χ ∧
      HalfPureSingletonFanFin10Atom0309 χ ∧
      HalfPureSingletonFanFin10Atom0319 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 4, 5, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0261 HalfPureSingletonFanFin10Atom0263
    HalfPureSingletonFanFin10Atom0264 HalfPureSingletonFanFin10Atom0267
    HalfPureSingletonFanFin10Atom0268 HalfPureSingletonFanFin10Atom0273
    HalfPureSingletonFanFin10Atom0277 HalfPureSingletonFanFin10Atom0278
    HalfPureSingletonFanFin10Atom0283 HalfPureSingletonFanFin10Atom0289
    HalfPureSingletonFanFin10Atom0297 HalfPureSingletonFanFin10Atom0298
    HalfPureSingletonFanFin10Atom0303 HalfPureSingletonFanFin10Atom0309
    HalfPureSingletonFanFin10Atom0319 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12788 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0261 χ ∧
      HalfPureSingletonFanFin10Atom0264 χ ∧
      HalfPureSingletonFanFin10Atom0265 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ ∧
      HalfPureSingletonFanFin10Atom0278 χ ∧
      HalfPureSingletonFanFin10Atom0279 χ ∧
      HalfPureSingletonFanFin10Atom0285 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ ∧
      HalfPureSingletonFanFin10Atom0298 χ ∧
      HalfPureSingletonFanFin10Atom0299 χ ∧
      HalfPureSingletonFanFin10Atom0305 χ ∧
      HalfPureSingletonFanFin10Atom0311 χ ∧
      HalfPureSingletonFanFin10Atom0321 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 4, 5, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 5, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0261 HalfPureSingletonFanFin10Atom0264
    HalfPureSingletonFanFin10Atom0265 HalfPureSingletonFanFin10Atom0268
    HalfPureSingletonFanFin10Atom0269 HalfPureSingletonFanFin10Atom0275
    HalfPureSingletonFanFin10Atom0278 HalfPureSingletonFanFin10Atom0279
    HalfPureSingletonFanFin10Atom0285 HalfPureSingletonFanFin10Atom0291
    HalfPureSingletonFanFin10Atom0298 HalfPureSingletonFanFin10Atom0299
    HalfPureSingletonFanFin10Atom0305 HalfPureSingletonFanFin10Atom0311
    HalfPureSingletonFanFin10Atom0321 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12789 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0262 χ ∧
      HalfPureSingletonFanFin10Atom0263 χ ∧
      HalfPureSingletonFanFin10Atom0264 χ ∧
      HalfPureSingletonFanFin10Atom0270 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ ∧
      HalfPureSingletonFanFin10Atom0273 χ ∧
      HalfPureSingletonFanFin10Atom0280 χ ∧
      HalfPureSingletonFanFin10Atom0281 χ ∧
      HalfPureSingletonFanFin10Atom0283 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ ∧
      HalfPureSingletonFanFin10Atom0300 χ ∧
      HalfPureSingletonFanFin10Atom0301 χ ∧
      HalfPureSingletonFanFin10Atom0303 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ ∧
      HalfPureSingletonFanFin10Atom0322 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 4, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0262 HalfPureSingletonFanFin10Atom0263
    HalfPureSingletonFanFin10Atom0264 HalfPureSingletonFanFin10Atom0270
    HalfPureSingletonFanFin10Atom0271 HalfPureSingletonFanFin10Atom0273
    HalfPureSingletonFanFin10Atom0280 HalfPureSingletonFanFin10Atom0281
    HalfPureSingletonFanFin10Atom0283 HalfPureSingletonFanFin10Atom0292
    HalfPureSingletonFanFin10Atom0300 HalfPureSingletonFanFin10Atom0301
    HalfPureSingletonFanFin10Atom0303 HalfPureSingletonFanFin10Atom0312
    HalfPureSingletonFanFin10Atom0322 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12791 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0262 χ ∧
      HalfPureSingletonFanFin10Atom0264 χ ∧
      HalfPureSingletonFanFin10Atom0265 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ ∧
      HalfPureSingletonFanFin10Atom0281 χ ∧
      HalfPureSingletonFanFin10Atom0282 χ ∧
      HalfPureSingletonFanFin10Atom0285 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ ∧
      HalfPureSingletonFanFin10Atom0301 χ ∧
      HalfPureSingletonFanFin10Atom0302 χ ∧
      HalfPureSingletonFanFin10Atom0305 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ ∧
      HalfPureSingletonFanFin10Atom0324 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 4, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0262 HalfPureSingletonFanFin10Atom0264
    HalfPureSingletonFanFin10Atom0265 HalfPureSingletonFanFin10Atom0271
    HalfPureSingletonFanFin10Atom0272 HalfPureSingletonFanFin10Atom0275
    HalfPureSingletonFanFin10Atom0281 HalfPureSingletonFanFin10Atom0282
    HalfPureSingletonFanFin10Atom0285 HalfPureSingletonFanFin10Atom0294
    HalfPureSingletonFanFin10Atom0301 HalfPureSingletonFanFin10Atom0302
    HalfPureSingletonFanFin10Atom0305 HalfPureSingletonFanFin10Atom0314
    HalfPureSingletonFanFin10Atom0324 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12792 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0263 χ ∧
      HalfPureSingletonFanFin10Atom0264 χ ∧
      HalfPureSingletonFanFin10Atom0265 χ ∧
      HalfPureSingletonFanFin10Atom0273 χ ∧
      HalfPureSingletonFanFin10Atom0274 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ ∧
      HalfPureSingletonFanFin10Atom0283 χ ∧
      HalfPureSingletonFanFin10Atom0284 χ ∧
      HalfPureSingletonFanFin10Atom0285 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ ∧
      HalfPureSingletonFanFin10Atom0303 χ ∧
      HalfPureSingletonFanFin10Atom0304 χ ∧
      HalfPureSingletonFanFin10Atom0305 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ ∧
      HalfPureSingletonFanFin10Atom0325 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 4, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 4, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0263 HalfPureSingletonFanFin10Atom0264
    HalfPureSingletonFanFin10Atom0265 HalfPureSingletonFanFin10Atom0273
    HalfPureSingletonFanFin10Atom0274 HalfPureSingletonFanFin10Atom0275
    HalfPureSingletonFanFin10Atom0283 HalfPureSingletonFanFin10Atom0284
    HalfPureSingletonFanFin10Atom0285 HalfPureSingletonFanFin10Atom0295
    HalfPureSingletonFanFin10Atom0303 HalfPureSingletonFanFin10Atom0304
    HalfPureSingletonFanFin10Atom0305 HalfPureSingletonFanFin10Atom0315
    HalfPureSingletonFanFin10Atom0325 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12793 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0266 χ ∧
      HalfPureSingletonFanFin10Atom0267 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ ∧
      HalfPureSingletonFanFin10Atom0270 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ ∧
      HalfPureSingletonFanFin10Atom0273 χ ∧
      HalfPureSingletonFanFin10Atom0286 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ ∧
      HalfPureSingletonFanFin10Atom0309 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ ∧
      HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 5, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0266 HalfPureSingletonFanFin10Atom0267
    HalfPureSingletonFanFin10Atom0268 HalfPureSingletonFanFin10Atom0270
    HalfPureSingletonFanFin10Atom0271 HalfPureSingletonFanFin10Atom0273
    HalfPureSingletonFanFin10Atom0286 HalfPureSingletonFanFin10Atom0287
    HalfPureSingletonFanFin10Atom0289 HalfPureSingletonFanFin10Atom0292
    HalfPureSingletonFanFin10Atom0306 HalfPureSingletonFanFin10Atom0307
    HalfPureSingletonFanFin10Atom0309 HalfPureSingletonFanFin10Atom0312
    HalfPureSingletonFanFin10Atom0326 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12794 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0266 χ ∧
      HalfPureSingletonFanFin10Atom0267 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ ∧
      HalfPureSingletonFanFin10Atom0270 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ ∧
      HalfPureSingletonFanFin10Atom0274 χ ∧
      HalfPureSingletonFanFin10Atom0286 χ ∧
      HalfPureSingletonFanFin10Atom0288 χ ∧
      HalfPureSingletonFanFin10Atom0290 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ ∧
      HalfPureSingletonFanFin10Atom0327 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 5, 6, 7, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 7, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0266 HalfPureSingletonFanFin10Atom0267
    HalfPureSingletonFanFin10Atom0269 HalfPureSingletonFanFin10Atom0270
    HalfPureSingletonFanFin10Atom0272 HalfPureSingletonFanFin10Atom0274
    HalfPureSingletonFanFin10Atom0286 HalfPureSingletonFanFin10Atom0288
    HalfPureSingletonFanFin10Atom0290 HalfPureSingletonFanFin10Atom0293
    HalfPureSingletonFanFin10Atom0306 HalfPureSingletonFanFin10Atom0308
    HalfPureSingletonFanFin10Atom0310 HalfPureSingletonFanFin10Atom0313
    HalfPureSingletonFanFin10Atom0327 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12795 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0266 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ ∧
      HalfPureSingletonFanFin10Atom0288 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ ∧
      HalfPureSingletonFanFin10Atom0308 χ ∧
      HalfPureSingletonFanFin10Atom0311 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ ∧
      HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 5, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0266 HalfPureSingletonFanFin10Atom0268
    HalfPureSingletonFanFin10Atom0269 HalfPureSingletonFanFin10Atom0271
    HalfPureSingletonFanFin10Atom0272 HalfPureSingletonFanFin10Atom0275
    HalfPureSingletonFanFin10Atom0287 HalfPureSingletonFanFin10Atom0288
    HalfPureSingletonFanFin10Atom0291 HalfPureSingletonFanFin10Atom0294
    HalfPureSingletonFanFin10Atom0307 HalfPureSingletonFanFin10Atom0308
    HalfPureSingletonFanFin10Atom0311 HalfPureSingletonFanFin10Atom0314
    HalfPureSingletonFanFin10Atom0328 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12796 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0267 χ ∧
      HalfPureSingletonFanFin10Atom0268 χ ∧
      HalfPureSingletonFanFin10Atom0269 χ ∧
      HalfPureSingletonFanFin10Atom0273 χ ∧
      HalfPureSingletonFanFin10Atom0274 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ ∧
      HalfPureSingletonFanFin10Atom0290 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ ∧
      HalfPureSingletonFanFin10Atom0309 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ ∧
      HalfPureSingletonFanFin10Atom0311 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ ∧
      HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 5, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 5, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0267 HalfPureSingletonFanFin10Atom0268
    HalfPureSingletonFanFin10Atom0269 HalfPureSingletonFanFin10Atom0273
    HalfPureSingletonFanFin10Atom0274 HalfPureSingletonFanFin10Atom0275
    HalfPureSingletonFanFin10Atom0289 HalfPureSingletonFanFin10Atom0290
    HalfPureSingletonFanFin10Atom0291 HalfPureSingletonFanFin10Atom0295
    HalfPureSingletonFanFin10Atom0309 HalfPureSingletonFanFin10Atom0310
    HalfPureSingletonFanFin10Atom0311 HalfPureSingletonFanFin10Atom0315
    HalfPureSingletonFanFin10Atom0329 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12797 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0270 χ ∧
      HalfPureSingletonFanFin10Atom0271 χ ∧
      HalfPureSingletonFanFin10Atom0272 χ ∧
      HalfPureSingletonFanFin10Atom0273 χ ∧
      HalfPureSingletonFanFin10Atom0274 χ ∧
      HalfPureSingletonFanFin10Atom0275 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ ∧
      HalfPureSingletonFanFin10Atom0313 χ ∧
      HalfPureSingletonFanFin10Atom0314 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ ∧
      HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 3, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 3, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0270 HalfPureSingletonFanFin10Atom0271
    HalfPureSingletonFanFin10Atom0272 HalfPureSingletonFanFin10Atom0273
    HalfPureSingletonFanFin10Atom0274 HalfPureSingletonFanFin10Atom0275
    HalfPureSingletonFanFin10Atom0292 HalfPureSingletonFanFin10Atom0293
    HalfPureSingletonFanFin10Atom0294 HalfPureSingletonFanFin10Atom0295
    HalfPureSingletonFanFin10Atom0312 HalfPureSingletonFanFin10Atom0313
    HalfPureSingletonFanFin10Atom0314 HalfPureSingletonFanFin10Atom0315
    HalfPureSingletonFanFin10Atom0330 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12798 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0276 χ ∧
      HalfPureSingletonFanFin10Atom0277 χ ∧
      HalfPureSingletonFanFin10Atom0278 χ ∧
      HalfPureSingletonFanFin10Atom0280 χ ∧
      HalfPureSingletonFanFin10Atom0281 χ ∧
      HalfPureSingletonFanFin10Atom0283 χ ∧
      HalfPureSingletonFanFin10Atom0286 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ ∧
      HalfPureSingletonFanFin10Atom0289 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ ∧
      HalfPureSingletonFanFin10Atom0316 χ ∧
      HalfPureSingletonFanFin10Atom0317 χ ∧
      HalfPureSingletonFanFin10Atom0319 χ ∧
      HalfPureSingletonFanFin10Atom0322 χ ∧
      HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 4, 5, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0276 HalfPureSingletonFanFin10Atom0277
    HalfPureSingletonFanFin10Atom0278 HalfPureSingletonFanFin10Atom0280
    HalfPureSingletonFanFin10Atom0281 HalfPureSingletonFanFin10Atom0283
    HalfPureSingletonFanFin10Atom0286 HalfPureSingletonFanFin10Atom0287
    HalfPureSingletonFanFin10Atom0289 HalfPureSingletonFanFin10Atom0292
    HalfPureSingletonFanFin10Atom0316 HalfPureSingletonFanFin10Atom0317
    HalfPureSingletonFanFin10Atom0319 HalfPureSingletonFanFin10Atom0322
    HalfPureSingletonFanFin10Atom0326 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12800 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0276 χ ∧
      HalfPureSingletonFanFin10Atom0278 χ ∧
      HalfPureSingletonFanFin10Atom0279 χ ∧
      HalfPureSingletonFanFin10Atom0281 χ ∧
      HalfPureSingletonFanFin10Atom0282 χ ∧
      HalfPureSingletonFanFin10Atom0285 χ ∧
      HalfPureSingletonFanFin10Atom0287 χ ∧
      HalfPureSingletonFanFin10Atom0288 χ ∧
      HalfPureSingletonFanFin10Atom0291 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ ∧
      HalfPureSingletonFanFin10Atom0317 χ ∧
      HalfPureSingletonFanFin10Atom0318 χ ∧
      HalfPureSingletonFanFin10Atom0321 χ ∧
      HalfPureSingletonFanFin10Atom0324 χ ∧
      HalfPureSingletonFanFin10Atom0328 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 4, 5, 6, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 5, 6, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0276 HalfPureSingletonFanFin10Atom0278
    HalfPureSingletonFanFin10Atom0279 HalfPureSingletonFanFin10Atom0281
    HalfPureSingletonFanFin10Atom0282 HalfPureSingletonFanFin10Atom0285
    HalfPureSingletonFanFin10Atom0287 HalfPureSingletonFanFin10Atom0288
    HalfPureSingletonFanFin10Atom0291 HalfPureSingletonFanFin10Atom0294
    HalfPureSingletonFanFin10Atom0317 HalfPureSingletonFanFin10Atom0318
    HalfPureSingletonFanFin10Atom0321 HalfPureSingletonFanFin10Atom0324
    HalfPureSingletonFanFin10Atom0328 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12802 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0280 χ ∧
      HalfPureSingletonFanFin10Atom0281 χ ∧
      HalfPureSingletonFanFin10Atom0282 χ ∧
      HalfPureSingletonFanFin10Atom0283 χ ∧
      HalfPureSingletonFanFin10Atom0284 χ ∧
      HalfPureSingletonFanFin10Atom0285 χ ∧
      HalfPureSingletonFanFin10Atom0292 χ ∧
      HalfPureSingletonFanFin10Atom0293 χ ∧
      HalfPureSingletonFanFin10Atom0294 χ ∧
      HalfPureSingletonFanFin10Atom0295 χ ∧
      HalfPureSingletonFanFin10Atom0322 χ ∧
      HalfPureSingletonFanFin10Atom0323 χ ∧
      HalfPureSingletonFanFin10Atom0324 χ ∧
      HalfPureSingletonFanFin10Atom0325 χ ∧
      HalfPureSingletonFanFin10Atom0330 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {2, 4, 6, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{2, 4, 6, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0280 HalfPureSingletonFanFin10Atom0281
    HalfPureSingletonFanFin10Atom0282 HalfPureSingletonFanFin10Atom0283
    HalfPureSingletonFanFin10Atom0284 HalfPureSingletonFanFin10Atom0285
    HalfPureSingletonFanFin10Atom0292 HalfPureSingletonFanFin10Atom0293
    HalfPureSingletonFanFin10Atom0294 HalfPureSingletonFanFin10Atom0295
    HalfPureSingletonFanFin10Atom0322 HalfPureSingletonFanFin10Atom0323
    HalfPureSingletonFanFin10Atom0324 HalfPureSingletonFanFin10Atom0325
    HalfPureSingletonFanFin10Atom0330 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12804 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0296 χ ∧
      HalfPureSingletonFanFin10Atom0297 χ ∧
      HalfPureSingletonFanFin10Atom0298 χ ∧
      HalfPureSingletonFanFin10Atom0300 χ ∧
      HalfPureSingletonFanFin10Atom0301 χ ∧
      HalfPureSingletonFanFin10Atom0303 χ ∧
      HalfPureSingletonFanFin10Atom0306 χ ∧
      HalfPureSingletonFanFin10Atom0307 χ ∧
      HalfPureSingletonFanFin10Atom0309 χ ∧
      HalfPureSingletonFanFin10Atom0312 χ ∧
      HalfPureSingletonFanFin10Atom0316 χ ∧
      HalfPureSingletonFanFin10Atom0317 χ ∧
      HalfPureSingletonFanFin10Atom0319 χ ∧
      HalfPureSingletonFanFin10Atom0322 χ ∧
      HalfPureSingletonFanFin10Atom0326 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {3, 4, 5, 6, 7, 8} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 6, 7, 8}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0296 HalfPureSingletonFanFin10Atom0297
    HalfPureSingletonFanFin10Atom0298 HalfPureSingletonFanFin10Atom0300
    HalfPureSingletonFanFin10Atom0301 HalfPureSingletonFanFin10Atom0303
    HalfPureSingletonFanFin10Atom0306 HalfPureSingletonFanFin10Atom0307
    HalfPureSingletonFanFin10Atom0309 HalfPureSingletonFanFin10Atom0312
    HalfPureSingletonFanFin10Atom0316 HalfPureSingletonFanFin10Atom0317
    HalfPureSingletonFanFin10Atom0319 HalfPureSingletonFanFin10Atom0322
    HalfPureSingletonFanFin10Atom0326 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

theorem halfPureSingletonFanFin10_clause12807 (χ : TripleColoring 10)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    ¬(HalfPureSingletonFanFin10Atom0297 χ ∧
      HalfPureSingletonFanFin10Atom0298 χ ∧
      HalfPureSingletonFanFin10Atom0299 χ ∧
      HalfPureSingletonFanFin10Atom0303 χ ∧
      HalfPureSingletonFanFin10Atom0304 χ ∧
      HalfPureSingletonFanFin10Atom0305 χ ∧
      HalfPureSingletonFanFin10Atom0309 χ ∧
      HalfPureSingletonFanFin10Atom0310 χ ∧
      HalfPureSingletonFanFin10Atom0311 χ ∧
      HalfPureSingletonFanFin10Atom0315 χ ∧
      HalfPureSingletonFanFin10Atom0319 χ ∧
      HalfPureSingletonFanFin10Atom0320 χ ∧
      HalfPureSingletonFanFin10Atom0321 χ ∧
      HalfPureSingletonFanFin10Atom0325 χ ∧
      HalfPureSingletonFanFin10Atom0329 χ) := by
  intro hbad
  have hnot : ¬IsStrongPolygonSet χ {3, 4, 5, 7, 8, 9} := by
    intro hstrong
    exact hnoStrong ⟨{3, 4, 5, 7, 8, 9}, by simp, by decide, hstrong⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  unfold HalfPureSingletonFanFin10Atom0297 HalfPureSingletonFanFin10Atom0298
    HalfPureSingletonFanFin10Atom0299 HalfPureSingletonFanFin10Atom0303
    HalfPureSingletonFanFin10Atom0304 HalfPureSingletonFanFin10Atom0305
    HalfPureSingletonFanFin10Atom0309 HalfPureSingletonFanFin10Atom0310
    HalfPureSingletonFanFin10Atom0311 HalfPureSingletonFanFin10Atom0315
    HalfPureSingletonFanFin10Atom0319 HalfPureSingletonFanFin10Atom0320
    HalfPureSingletonFanFin10Atom0321 HalfPureSingletonFanFin10Atom0325
    HalfPureSingletonFanFin10Atom0329 at hbad
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [HalfPureSingletonFanFin10StrongQuad]

end ErdosSzekeres

end
