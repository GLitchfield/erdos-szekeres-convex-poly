module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 088. -/

theorem fin15Anchored_clause11264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1291 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1291 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11265 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1293 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0218 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1293 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1293 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0218 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1293 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1297 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0218 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1297 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1297 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0218 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1297 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11269 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1298 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0219 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1298 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1298 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0219 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1298 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1298 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0216 Fin15AnchoredAtom0219 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1298 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11272 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1303 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0219 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1303 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1303 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0219 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1303 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1303 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0219 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1303 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11275 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1304 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0220 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1304 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11276 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1304 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0220 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1304 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1304 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0220 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1304 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1304 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0218 Fin15AnchoredAtom0220 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1304 at hbad
  cases hcolor0 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11279 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1305 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0219 Fin15AnchoredAtom0220 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1305 at hbad
  cases hcolor0 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11280 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1305 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0219 Fin15AnchoredAtom0220 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1305 at hbad
  cases hcolor0 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11281 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1305 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0219 Fin15AnchoredAtom0220 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1305 at hbad
  cases hcolor0 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1305 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0219 Fin15AnchoredAtom0220 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1305 at hbad
  cases hcolor0 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11283 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0222 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1306 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11284 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0222 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1306 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11285 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0222 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1306 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0222 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1306 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0222 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1306 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11288 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0223 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1307 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11289 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0223 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1307 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11290 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0223 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1307 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11291 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0223 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1307 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11292 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0223 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1307 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0223 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1307 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0223 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1307 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0223 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1307 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0223 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1307 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11297 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0224 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1308 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11298 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0224 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1308 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11299 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0224 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1308 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11300 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0224 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1308 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11301 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0224 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1308 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0224 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1308 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0224 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1308 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0224 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1308 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0224 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1308 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11306 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0225 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1309 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11307 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0225 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1309 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11308 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0225 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1309 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11309 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0225 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1309 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11310 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0225 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1309 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0225 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1309 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0225 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1309 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11313 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0225 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1309 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0221 Fin15AnchoredAtom0225 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1309 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11315 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0223 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1310 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11316 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0223 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1310 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11317 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0223 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1310 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11318 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0223 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1310 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0223 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1310 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0223 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1310 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0223 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1310 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0223 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1310 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11323 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0223 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1310 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11324 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1311 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0224 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1311 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11325 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1311 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0224 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1311 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1311 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0224 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1311 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11327 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1312 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0225 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1312 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11328 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1312 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0225 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1312 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11329 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1312 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0225 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1312 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1312 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0225 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1312 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1312 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0222 Fin15AnchoredAtom0225 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1312 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11332 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0224 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1313 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11333 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0224 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1313 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11334 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0224 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1313 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11335 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0224 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1313 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11336 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0224 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1313 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0224 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1313 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0224 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1313 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0224 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1313 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11340 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0224 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1313 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0224 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1313 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0224 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1313 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11343 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0225 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1314 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11344 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0225 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1314 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11345 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0225 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1314 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11346 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0225 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1314 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0225 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1314 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0225 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1314 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0225 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1314 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0223 Fin15AnchoredAtom0225 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1314 at hbad
  cases hcolor0 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11351 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0224 Fin15AnchoredAtom0225 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1315 at hbad
  cases hcolor0 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11352 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0224 Fin15AnchoredAtom0225 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1315 at hbad
  cases hcolor0 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11353 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0224 Fin15AnchoredAtom0225 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1315 at hbad
  cases hcolor0 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11354 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0224 Fin15AnchoredAtom0225 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1315 at hbad
  cases hcolor0 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0224 Fin15AnchoredAtom0225 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1315 at hbad
  cases hcolor0 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0224 Fin15AnchoredAtom0225 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1315 at hbad
  cases hcolor0 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0224 Fin15AnchoredAtom0225 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1315 at hbad
  cases hcolor0 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0224 Fin15AnchoredAtom0225 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1315 at hbad
  cases hcolor0 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0224 Fin15AnchoredAtom0225 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1315 at hbad
  cases hcolor0 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11360 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0227 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1316 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11361 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0227 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1316 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11362 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0227 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1316 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11363 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0227 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1316 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0227 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1316 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0227 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1316 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0227 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1316 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11367 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1317 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0228 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1317 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11368 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1317 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0228 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1317 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1317 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0228 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1317 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1317 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0228 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1317 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1317 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0228 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1317 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1318 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0226 Fin15AnchoredAtom0229 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1318 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11373 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0228 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1319 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11374 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0228 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1319 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11375 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0228 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1319 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11376 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0228 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1319 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11377 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0228 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1319 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0228 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1319 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0228 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1319 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11380 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0228 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1319 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0228 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1319 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0228 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1319 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11383 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0229 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1320 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11384 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0229 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1320 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11385 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0229 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1320 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11386 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0229 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1320 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0229 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1320 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0229 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1320 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0229 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1320 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0229 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1320 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0227 Fin15AnchoredAtom0229 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1320 at hbad
  cases hcolor0 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
