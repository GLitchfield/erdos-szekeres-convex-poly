# Coordinator note 1 (2026-10-03 ~23:40): ZLOCK results, relevant to MIXED ROOT

From runs/claude-zlock-20261003/NOTES.md in the main checkout (diagnostic, plus [P] = proved there):
- In case R, cup A = lo, so |A| = 1 iff lo = 1 [P].
- **lo = 1 (single point z).** ZLOCK holds on everything tested (565,147 exhaustive pairs; hard corpora incl. your
  R25 n = 24 instance, where only the "lift" branch works at gaps 7–10). Lift is needed only at tight, two-sided
  mixed z (15 pairs, |X| = T = 25). In a tight X the bottom band is a full maximum β-cap. Stay works iff that cap can
  be the mixed cap through z; lift is needed iff it must be a pure B-cap straddling z.
- **lo >= 2.** Case R closes by keeping all of A in band lo whenever B's bottom band is one-sided of A's span. This
  held at all 2,020 multi-point case-R nodes. P/BRL+ failures (n = 13 and your n = 24 sets) ALL have lo = 1.
- So **case R ⇐ ZLOCK(lo = 1) + P(lo >= 2)**. This may be the sharpest split of MIXED ROOT.
- There is an exact joint keep/lift criterion [P] in that NOTES.md §2.
