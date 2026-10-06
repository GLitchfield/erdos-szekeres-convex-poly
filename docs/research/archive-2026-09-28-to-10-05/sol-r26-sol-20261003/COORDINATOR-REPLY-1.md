# R26 response to coordinator note1

2026-10-04 04:40 UTC. Read COORDINATOR-NOTE-1.md and the current primary
claude-zlock-20261003/NOTES.md fully. No external message was sent.

The empirical assertion that lift-only parents are always tight is now
superseded. R26 has an exact singleton MIXED ROOT with parent n24<capacity25,
cup4/cap5/strong6, regional child cap ranks4/4, no valid z-bottom map,
and a directly checked z-band2 map. It is the retained n25 gap7 parent
after deleting old child point0; the new z gap is6. Independent complete
one-change BT and all-triple Glucose4 agree. Strong7 is excluded using
defining-quad SAT; a strong6 set is explicit. DRAT is retained but not
independently checked. All23 further B-point deletions preserve the ranks
and mixedness and restore stay, so this is locally deletion critical.

Evidence: slack-stay-independent.json (job20261003-232648-2a978c),
slack-stay-deletion-classification.json (233410-55f3d8), and
MIXED-ROOT.md section8. This refutes the tightness-only helper, not ROOT
or ZLOCK. Do not restrict the open singleton obligation to tight parents.

The sufficient split into ZLOCK(lo1) and P(lo>=2) agrees with R26. A proved
P at an appropriate A extremum or the whole core would position bottom on
one side of A's span and keep all A; empirical success is not a proof.
R26's joint KEEP/LIFT equivalence agrees with NOTES section2, including
the two-lower-endpoint interval condition. Sequential singleton insertion
changes colors for general A. Unrestricted singleton ROOT allows z in
any band; equating it with just stay/lift still needs normalization.

New paper constructions, not Lean credit:

- General ROOT closes when strong(B)=cap(B): a root induction supplies an
  outer whole-cap transversal, whose removal gives strict strong slack.
- With B=L<<U, cL<=p+2,dU<=beta-2, a three-band ROOT closes by partitioning
  A+L in the first two bands and placing U in the third. All m close under
  the extra strict strong slack sigmaU<s.
- A full-child nested singleton family closes when both anchors share a
  deeper open cap core (section13).
- A full-child pair-anchor family closes when a,b immediately surround a
  CLOSED deeper core point h (section16). Choose last cap endpoints for
  z>h, first endpoints for z<h; put the opposite anchor at2. The localized
  frame controls the regional cap overflow without a deeper open core.

The attempted cap-chain uncrossing invariant is independently refuted:
decomposable Ucup3/cap4/strong5 has open core(2,4), but core cap3 and no
maximum cap attaining both extrema. Tree/complete cap family are in
joint-cap-endpoints-independent.json, job20261004-002704-bc62fd. Its
anchored n10 ROOT still has a bottom repair. Core endpoint bounds do not
give joint interval-chain attainment. Section16 also gives an exact beta6
ROOT whose child's open core has only cap3, disproving a nearmaximum
core-rank shortcut. Full singleton ROOT remains unproved/unrefuted.
