module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 252. -/

theorem fin15Anchored_clause32256 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0038 at hbad
  have hr := hanchor (i := 4) (j := 6) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32257 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0039 at hbad
  have hr := hanchor (i := 4) (j := 7) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32258 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0040 at hbad
  have hr := hanchor (i := 4) (j := 8) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32259 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0041 at hbad
  have hr := hanchor (i := 4) (j := 9) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32260 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0042 at hbad
  have hr := hanchor (i := 4) (j := 10) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32261 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0043 at hbad
  have hr := hanchor (i := 4) (j := 11) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32262 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0044 at hbad
  have hr := hanchor (i := 4) (j := 12) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32263 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0045 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0045 at hbad
  have hr := hanchor (i := 4) (j := 13) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32264 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0046 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0046 at hbad
  have hr := hanchor (i := 4) (j := 14) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32265 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0047 at hbad
  have hr := hanchor (i := 5) (j := 6) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32266 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0048 at hbad
  have hr := hanchor (i := 5) (j := 7) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32267 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0049 at hbad
  have hr := hanchor (i := 5) (j := 8) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32268 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0050 at hbad
  have hr := hanchor (i := 5) (j := 9) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32269 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0051 at hbad
  have hr := hanchor (i := 5) (j := 10) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32270 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0052 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0052 at hbad
  have hr := hanchor (i := 5) (j := 11) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32271 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0053 at hbad
  have hr := hanchor (i := 5) (j := 12) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32272 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0054 at hbad
  have hr := hanchor (i := 5) (j := 13) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32273 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0055 at hbad
  have hr := hanchor (i := 5) (j := 14) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32274 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0056 at hbad
  have hr := hanchor (i := 6) (j := 7) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32275 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0057 at hbad
  have hr := hanchor (i := 6) (j := 8) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32276 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0058 at hbad
  have hr := hanchor (i := 6) (j := 9) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32277 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0059 at hbad
  have hr := hanchor (i := 6) (j := 10) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32278 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0060 at hbad
  have hr := hanchor (i := 6) (j := 11) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32279 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0061 at hbad
  have hr := hanchor (i := 6) (j := 12) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32280 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0062 at hbad
  have hr := hanchor (i := 6) (j := 13) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32281 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0063 at hbad
  have hr := hanchor (i := 6) (j := 14) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32282 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0064 at hbad
  have hr := hanchor (i := 7) (j := 8) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32283 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0065 at hbad
  have hr := hanchor (i := 7) (j := 9) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32284 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0066 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0066 at hbad
  have hr := hanchor (i := 7) (j := 10) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32285 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0067 at hbad
  have hr := hanchor (i := 7) (j := 11) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32286 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0068 at hbad
  have hr := hanchor (i := 7) (j := 12) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32287 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0069 at hbad
  have hr := hanchor (i := 7) (j := 13) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32288 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0070 at hbad
  have hr := hanchor (i := 7) (j := 14) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32289 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0071 at hbad
  have hr := hanchor (i := 8) (j := 9) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32290 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0072 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0072 at hbad
  have hr := hanchor (i := 8) (j := 10) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32291 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0074 at hbad
  have hr := hanchor (i := 8) (j := 12) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32292 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0075 at hbad
  have hr := hanchor (i := 8) (j := 13) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32293 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0076 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0076 at hbad
  have hr := hanchor (i := 8) (j := 14) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32294 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0077 at hbad
  have hr := hanchor (i := 9) (j := 10) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32295 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0078 at hbad
  have hr := hanchor (i := 9) (j := 11) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32296 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0079 at hbad
  have hr := hanchor (i := 9) (j := 12) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32297 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0080 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0080 at hbad
  have hr := hanchor (i := 9) (j := 13) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32298 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0081 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0081 at hbad
  have hr := hanchor (i := 9) (j := 14) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32299 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0082 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0082 at hbad
  have hr := hanchor (i := 10) (j := 11) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32300 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0083 at hbad
  have hr := hanchor (i := 10) (j := 12) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32301 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0084 at hbad
  have hr := hanchor (i := 10) (j := 13) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32302 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0085 at hbad
  have hr := hanchor (i := 10) (j := 14) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32303 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0086 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0086 at hbad
  have hr := hanchor (i := 11) (j := 12) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32304 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0087 at hbad
  have hr := hanchor (i := 11) (j := 13) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32305 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0088 at hbad
  have hr := hanchor (i := 11) (j := 14) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32306 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0089 at hbad
  have hr := hanchor (i := 12) (j := 13) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32307 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0090 at hbad
  have hr := hanchor (i := 12) (j := 14) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

theorem fin15Anchored_clause32308 (chi : TripleColoring 15)
    (hanchor : chi.IsAnchored) :
    ¬(Fin15AnchoredAtom0091 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0091 at hbad
  have hr := hanchor (i := 13) (j := 14) (by decide) (by decide)
  rw [hbad] at hr
  cases hr

end ErdosSzekeres

end
