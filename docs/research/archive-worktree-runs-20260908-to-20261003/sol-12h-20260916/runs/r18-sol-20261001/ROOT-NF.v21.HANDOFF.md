# R18 accepted partial ROOT-NF v21 checkpoint — 2026-10-02 02:10 UTC

Branch node/CtxOneLevelRootBoundNormalForm; commit
09395dfc6e2f254881b29899625b250fb2ef2062, via guarded commit job
20261001-220925-0d6099. Exactly three files: proof module, registered falsifier,
fresh falsifier receipt. Working tree clean; original configuration restored
byteexact20G and temporary elaborate_memory_min12G removed before commit.

General ROOT-NF and C1r remain OPEN. No theorem credit is claimed for this
checkpoint. Registered statement and FULL strong child-count P(n) are byteexact
the accepted v8, type e0cedb9ee88cc591. Source
8a449f900130641c80d06183e7f562fd9704f94f6cd473229e7815246107a17e
has exactly three ESBlueprint holes at lines11310/11312/11315.

Original-source targeted audit20261001-215313-b23d04 DONE/rc0,896.3s/8687MiB,
12G matched initial floor and outer reservation, no OOM or chosen timeout.
Receipt ROOT-NF.v21.FINAL.ORIGINAL-AUDIT.RECEIPT.json,
SHAbec76eef3a15361dee1688a227e950336546a6153ea13e1204fd4182ac5c5ccc.
Exact type_pp unchangedv8, locktrue, sorrytrue; axioms only
propext/Classical.choice/Quot.sound/sorryAx; blocked_byempty.
Full JOB-LOG.json and JOB.DONE.json preserved; declared stdout --out is missing
because it was not a redirect. The full job journal is authoritative.

Compiling proof progress: empty/unit/single-run, axis-two, saturated maximum,
chosen-global-three and opposite-global-three slices discharge their equalities.
The residual multirun domain has a,u>=4,k>=4,1<=m<=k-3 and numRuns>=2.
An actual legal same-side part with a removed genuine child merges to a uniform
one-level root with the same a/u/k, maximum max(c,m), and identical genuine
child positions. Strict part/complement child-count inequalities allow FULL
P(j) to give its actual bound <= the merged root's complete normal-form bound.

Let rest := sigma.childPositions.filter (fun p => p notin block) and d'=k-1-d.
For each actual interval block and1<=d<=k-2 the upper holes are:
  (sigma.part block lower d).bound + (sigma.part rest upper d').bound <= tau.bound
  (sigma.part block upper d').bound + (sigma.part rest lower d).bound <= tau.bound.
The third hole is tau.bound<=sigma.bound, by constructing actual witnessing cuts.
Independent component domination is false; same-side transport alone does not
couple the opposite component's marker threading. Keep the sum as the obligation.

Meaningful failed compiler routes: v19 default4G OOM212030-a608c4; auto12G retry
refused above outer4G. Matched12G v19 212636-6ae588 failed dependent Side/hletters
conversions, opaque sigma globals in omega and record layout. v20
213817-81c348 failed only a record-maximum simplification; v21 adds h_rho_max.
First v21 215038-307020 was refused preLean by concurrent falsifier's worktree
reservation. All full statuses/joblogs and prior sources are preserved and logged
before each body-only repair. No force, cancellation or statement change.

The falsifier had omitted appending right-end markers. Prior broad right/both
endpoint coverage claims are withdrawn; old29520/157680 raw checks represented
9840/52560 unique parameter+word records with Side, all right-unmarked.
Certified Lean receipts are unaffected. One-line repair source
a2ea44c0477f4c803f7e4470c18079dcb11a81f84a8e04066fa183b18760be40.
Fresh official falsify20261001-215037-988759 PASS29520; corrected wider seven
shards PASS157680; explicit five-child family213909-5a63da PASS128.
Exact inputs, scope/source identities and all terminal statuses are in
ROOT-NF.DIAGNOSTIC-COVERAGE-CORRECTION.md and referenced full receipts.
No Python/C-to-Lean semantic-equivalence theorem exists; diagnostics have no
theorem credit. The endpoint input regression220553-52a9ff passes10subcases
and preserved oldbug negativecontrol; failed pytest attempt220508-7ddedd preserved.

Reusable public results: twelve CLOSED original-source nodes, exact commits/
types/receipts in REPORT.sol.md and per-node handoffs. Private accepted Opp3
classifier and same-side carrier have independent receipts; they are local
proofs in this checkpoint, not additional public CLOSED nodes.
The public61line same-side bridge is prepared but not yet registered here.
Public large Opp3 publication is deferred for this run.

Safest next mathematics: ordered paired-profile transport on actual cut
components, preserving endpoints/threading, together with full smaller-root IH.
A proposed general F(C) lower-witness route is explicitly UNPROVED/UNCODED in
ROOT-NF.GENERAL-LOWER-ROUTE.UNPROVED.md. Broad n5otherparameters/n6/n7 remain
open; do not substitute finite diagnostic evidence for either missing inequality.

es search before writing the same-side/root/max(c,m) lemmas returned no indexed
equivalent (shared index stale). Reused closed same-side merge, legal part/WF
and positional child lemmas; no full extract or existing statement edit.
