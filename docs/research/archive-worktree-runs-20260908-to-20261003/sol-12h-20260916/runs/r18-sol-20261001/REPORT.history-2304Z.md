# R18 Sol research report — active draft

Status at2026-10-01T22:39Z: Part1 complete. Eight original-source CLOSED commits.
Full ROOT-NF and C1r OPEN. ScopedNF/root-reachable failure/boundary unit drafts pending.
Single configured gpt-6.1-sol at xhigh; no delegation, merge, push, primary
tracked-source edits, existing statement edits, full extract, or new trial.
Research windowwindow-bff1ef2d0f4547b3 remains active. Final usage/code review
and final handoff are pending; this report is a checkpoint, not task completion.

## Accepted Lean results

| Result | Branch / commit | Receipt and status |
|---|---|---|
| C1r from full ROOT-NF as an explicit hypothesis | node/CtxBoundChildRunContractionOneLevelRootOfNormalForm / 6cc98c1f9dff6d7577cbe424b9756b62a4810149 | isolated123546-843746 accepted; final123704-d45ee0 CLOSED, typefee0a07f9cb0f06, receipt3d7b5f4195ff1e1be384247419ebf66a5a4b7458c63929310201010883e351a9 |
| Proper part on a global axis<=2 has bound0 when it omits any genuine child | node/CtxPartBoundZeroOfUnitGlobalAxisAndRemovedChild / 298a3661e45f15e7dadc728ee4f9e67b3c949fe7 | isolated132235-01b6f9 accepted; final132328-d90057 CLOSED, type59d3fffe846cf5be, receipt1097e9da1c118e5b4d2d2354d580477be12312299c67ea4da64b270baab1547c |
| Raw one-level single-run endpoint-presence normalization | node/CtxOneLevelSingleRunBoundNormalForm / 8cd359e6c71ec20d80ab1254f7a97999d4f5a5f1 | isolated134427-e4b930 accepted; final134527-879206 CLOSED, type30723e3b90f91c84, receipt37aa6a229f6a6446c562fefb90e4ffec6b2b79821e1ff17c15d655d94df14d9c |
| Exact two-level unilateral marker-thread extension profile | node/CtxTwoLevelUnilateralYoungMarkerExtensionsExact / 766e182f1a8f192b44cdbcf3c1ba1a33911857c2 | isolated142500-142ecd accepted; final142601-2cf951 CLOSED, type88855bc6fde5dd3d, fullreceiptfc98593b6e9606ff2e05e4e002bb2cfe70d197ba16577643df922f7a1c37bf26 |
| Positive bound with opposite axis<=2 reaches a positive same-axis single-run leaf with full history provenance | node/CtxPositiveBoundHasSameAxisSingleRunLeaf / f1333e313f2efd926430418d0b2a0bc08f6b7e08 | isolated144316-1c879a accepted; final144428-968d72 CLOSED, typeaeede1816e300ae, receiptf25ba155b76648ad6725550de71f583c39ba8ea19cb740d5fbe741c37ae652a2 |
| One protected child bracketed by selected old markers annihilates every-fuel/full bound when chosen global<=3 and opposite<=2 | node/CtxBoundZeroOfProtectedBracketedChildAndOppositeUnitAxis / 6d9fbdda82e2ab99fc7f8dff65c4c3b0f3d757dd | isolated161014-d7696e accepted; final161310-076303 CLOSED, typef5d6f67d88632043, receipt902af3332976f906317567dc6560221fe7beec2ac36542075b331800fcb7eb03 |
| First-child singleton and source both have bound1 with opposite global2, chosen>=4+old-left indicator, old m<=k-3 | node/CtxFirstChildSingletonBoundOneOfOppositeUnitAxis / e02d9a81fd0a9f81965d681e985f22a57c605da3 | isolated170109-02c805 accepted; final170229-f9f1f4 CLOSED, type65d4019b78e927, receipta828ac078319223ed8927768f4ab461b995684420a3bd5a277ef92ee9b95184a |
| Arbitrary uniform two-run root with unmarked ends and opposite global2 has bound1 at chosen>=3/old m<=k-3 | node/CtxTwoUnmarkedRunsBoundOneOfOppositeUnitAxis / b61c3b6bbe88b705d2ea6e702eaf180351d96f6d | isolated182223-7983b1 accepted; original guarded targeted182853-b90582 CLOSED, type97ffc56385043289, receipt0bc6ca2f7d439edba6dbea756e9ad110bc8adf81fc2ae46b254b24493ff78390 |

All eight original-source closed results use only propext,Classical.choice,Quot.sound, preserve
their exact registered statements, and have no sorry. They are separate
main-based one-node branches. The conditional result does not import or use
the open ROOT-NF theorem. Exact hypotheses and proof receipts are in
C1R-FROM-NF.HANDOFF.md,AXIS-TWO-PART-ZERO.HANDOFF.md,SINGLE-RUN-NF.HANDOFF.md,
TWO-LEVEL-UNILATERAL.HANDOFF.md,UNIT-AXIS-LEAF.HANDOFF.md,PROTECTED.HANDOFF.md,
FIRST-CHILD.HANDOFF.md,TWO-UNMARKED.HANDOFF.md. All eight are committed.
Critical guardedcommit183806-2049fb DONE,threefiles/clean. The following
paragraphs retain earlier checkpoint history; latest states above govern.
Positive local bundle164923-957f45/op-51951f582ac94ae2 failed11errors, second
165108-72ae2e failed3constructor contradictions; both preserved/logged before
repairs. Third165208-732d73/op-6fddc92520f4483b ACCEPTED14.784s2109MiB on fresh
committed-source fixturefb6c5d6c8e11c75f3e362a572fffc82bc982897d0f76031a2da9c49f06a78de0.
It tests the independent321line first-singleton and593line arbitrary two-run
lower drafts locally. Never install it or assign public positive theorem credit;
all three jobs terminal, source unchanged throughout that sequence.

First-child singleton public node registered on its own current-main branch
node/CtxFirstChildSingletonBoundOneOfOppositeUnitAxis, actual base
4a990c3f159168994ae08f4cbff511e952371df0. Registration165350-ecdfe0 DONE379.4s2299MiB,
exacttype65d4019b78e927. Local cap restored exact20G;378inherited lock records/
19metadata repaired preserving every type. Standalone170109-02c805 ACCEPTED
9.644s2102MiB/std only, receipt726895836679624aa8cdd7c2b635129beda44c85871f9a6eb55ba8b496a62fa8.
Identical323line body-v2 installed; original-source targeted170229-f9f1f4
DONE/CLOSED6.2677s641MiB with exacttype/lock/no sorry. Final receipt
a828ac078319223ed8927768f4ab461b995684420a3bd5a277ef92ee9b95184a.
Commit171028-14f797 DONE, SHAe02d9a81fd0a9f81965d681e985f22a57c605da3,
3files/clean. Handoff updated and claim released CLOSED.

Raw root-data/WF/conditional-reflection geometry bundle171258-5dcc57/
op-b75e972d9f064ded ACCEPTED14.1878s2103MiB,1083lines, fresh installed-source
fixture26c57396e72e7b946cd169e5987a26fcda709d62ce3bb2b7609784936c2bd441.
Reflection takes reverse-bound equality explicitly; any final legal-root
caller must establish WF and invoke closed ctx_bound_reverse. Unchecked
zero fragments and UNIT-AXIS-CLASSIFICATION.PLAN.md are separate drafts.
New107line EXTREME-FRESH-THREE raw strengthening is submitted in isolated
local check173919-7c11cc/op-15f12d9fe0084caf on existing closed fresh-four
carrier, fixture8dce1f8637c41d14607d1125264ed1cc26fe5198055f02e1aec1f89d04e84131.
It ACCEPTED9.107s2105MiB, stagefa64ead87a7790da55e1de534b811f479fbfc1a5d29db1d44abf456dee2f04bd.
Both local bundles use only standard axioms; no new public theorem credit.
All three own jobs terminal; seven originals committed. Current queue admission
resumed but its cause remains unverified.
Current configured40G admission would fit observed20G live + aged20G queued;
a cached30G worker cap remains an unverified hypothesis, with no intervention.

Marked-head root positive corollary passed local bundle170110-5b98a9,
12.999s2103MiB/std/exactparent, receipta3e29bf383ab3f061a5c2b34a594cb979d13082e53aeaa09a438f645d4a1e533.
It is not separately registered/public. Prepared ROOT-NF.induction-v10.source.lean.txt
2507lines/3holes combines locally accepted three-run zero and positive lower
proofs with the FULL smaller-root equality IH. Additional finite normal-word
cases remain UNCHECKED/UNINSTALLED; actual NF branch claim/recheck required.

## ROOT-NF registration and actual induction

ROOT-NF typee0cedb9ee88cc591 retains endpoint presence, maxima=[m], and one
child per run clamped at3 when a=2 oru=2, otherwise2. Registration commit
1223439dd88c35d6c0c6d07b931b6cf528a4b3da on
node/CtxOneLevelRootBoundNormalForm from mainb231fee6. Official targeted
check115504-d79ec9 confirms compiling OPEN conjecture and exacttype, not proof.

Actual strong-child induction v5 committed e5d95acfad66fe8130afeca86ee94e62283eb226.
The IH covers full smaller ROOT-NF for all legal globals/maxima/sides/words.
Unit/empty cases and both strict proper-part child-count decreases compile.
v6 locally reuses accepted single-run proof and compiles in targeted
135344-d93c3b,7.56s625MiB,receipt
f1af18f847d260901281774ad0517f18afbfb9ec9984ca0bfa80db44be4f0d42.
Three intentional mathematical holes remain: both paired interval-cut upper
inequalities and NF<=source. No ROOT-NF theorem credit is claimed.

v7 moved full single-run equality before antisymmetry and added an axis-two
positive-normal upper shortcut using the already-closed common-singleton-rank
theorem. Check140242-356691 failed a dependent-match elaboration defect; source,
status and compiler output are preserved/logged. v8 repairs the scalar match
with an explicit Side function; check140511-cb43c3 DONE,7.98s640MiB,
exacttype/lock unchanged, expected sorryAx only. Receipt
2395afde00833b1593e4532e4b27f24dcc7ed5d4a7d1860ddfbb3f2ad1db4911.
Committed fc037f7fc2eac7f283dc8dfe27b3daa73c46172f, with three remaining
holes and no theorem credit. NF claim released PARTIAL before helper branch;
exact handoff ROOT-NF.v8.HANDOFF.md. C1r claim remains active.

## Diagnostic findings and failed routes

Official ROOT-NF falsifier114749-eba325 passed29520/29520 legal k3/4 roots.
Frozen-source wider job133422-a41c9d passed157680/157680 legal k5/6 roots in
1309.3s87MiB. Both cover children1..4,all compositions,alllegalglobals/maxima,
both sides,endmultiplicity0/1/2,separators1/2. No counterexample found.
These C results have no formally certified semantic equivalence to Lean.

Componentwise free NF-cut domination failed12992/254160 cuts despite zero
paired-sum/NF failures (113221-5d305b). Absorb/relabel failed336 components
(114206-b197f9). Absorb/delete passed both-end63540cuts (114501-b24249) but
its all-end extension failed9720 candidate sums, all no-end (115602-22d1a0).
All failed scopes and witnesses remain recorded; no actual NF equality failed.

The legal root a=u5,k6,m1,[S,S,1U,S,S] has a cut whose complement is exactly
the already Lean-certified general-C1 12->9 counterexample. Same-cut values
drop(1,12)->(1,9); reoptimization restores total13 diagnostically
(122825-18f2b7). Thus an individually contraction-stable part class closed
under all root cuts cannot support the desired induction. Joint transport
or coupling/orientation reoptimization is necessary.

Axis-two Boolean probe124627-f7b5d4 passed50400/50400 roots. It suggests a
one-contributing-path interpretation, recorded precisely in
AXIS-TWO-THREAD-INTERPRETATION.md. The old opposite global2 case appears to
have bound1 exactly when m<=k-3 and chosenG>=e+3+[e=0 andruns>=3]. The
all-path lower extension-cost/zero criterion remains unproved.

Exact two-child normal C/D formula passed18048 legal k3..10 cases
(130659-09192b); its fixed normal-cut Lean draft is deferred/unregistered.
The unilateral two-level ordered-fold candidate passed219120 comparisons
(140056-e050f8,5.8s23MiB), using shared extension and lean=True limit APIs.
The two-level profile is now registered as
ctx_two_level_unilateral_young_marker_extensions_exact, type88855bc6fde5dd3d.
First isolated check142500-142ecd/op-bc3028fed1a2444b accepted with standard
axioms only. Original-source targeted check142601-2cf951 CLOSED,3.944s580MiB,
no sorry, only standard axioms. Commit766e182f, clean independent branch,
claim released CLOSED. It addresses the exact profile for arbitrary physical
word length, not the all-path minimum.

Additional explicit larger-child pilots141337-6802f1 and141844-faf62e passed
no-end alternating roots a=u=k=7,m=1,lower, with four/five/six children; both
source and NF have value31. Five children took1.032s, six316.81s/354MiB.
Repeating the identical six-child case with8M memo entries142511-6e5c43 took
298.40s/1390MiB: only~6% faster at~4x memory, so no useful saving is claimed.
Broad six-child/7+ coverage remains open. Both timing runs completed, with
no cancelled or silently narrowed scope.

Next same-trial candidate UNIT-AXIS-LEAF.signature-v2/body-v4 is registered,
typeaeede1816e300ae. Initial registration143331-5b3a1a failed reserved binder
prefix and rolled back node creation; diagnostics preserved/logged. Binder
history repair retry143457-28f79b DONE348.3s2296MiB, local20G cap restored
byte-exact before capture. Isolated proof144141-3f7407/op-00c00385bfad474d
FAILED a basecase equality and costly Side simplification; preserved/logged
before repair. Second isolated144316-1c879a/op-e1bfd440b110403d ACCEPTED
with only standard axioms. Identical body-v4 is installed; original-source
144428-968d72 CLOSED, build5.05s614MiB, exacttype/lock intact and standard
axioms; committedf1333e313f2efd926430418d0b2a0bc08f6b7e08 via155814-0555bb.
Claim released CLOSED with UNIT-AXIS-LEAF.HANDOFF.md.
It follows a positive chosen-axis path when the opposite global
is<=2 to a positive one-run base, preserving globals/positions, legal
prepended maxima, shifted original levels and chosen-side removed children.
It reuses R15 positive interval-cut attainment and the accepted R18 raw zero
argument locally. This would expose the marker-order cost at every positive
leaf, rather than assert another scalar-erasure transport. Pure geometric
THREE-SITE-SHADOW signature/body-v1 is prepared UNREGISTERED/UNCHECKED:
a one-run shadow of three child sites separated by two old markers forces
two extension slots, reusing accepted raw interval and ordered fold proofs.
THREE-RUN-WITNESS supplies the first three run starts and predecessor markers.
AXIS-THREE-ROOT-ZERO.body-v1.txt assembles755lines locally: raw uniform one-level
root, chosen global<=3, opposite global<=2 and at least three runs imply bound0.
The composition/geometric components passed isolated local bundle151331-97797f,
11.88s2103MiB; receipt3c1d219a4d889f6ef7f7e14c4a09758ca835c8606c9b6ca21e86eec763ee8eb3.
This checks a local fact inside the leaf statement; no public zero node credit.
Both original and bundle are terminal, source unchanged.

Latest R16 final inventory already closes endpoint-small-axis and saturated
old-maximum zeros. Own endpoint-zero and saturation drafts are DEFERRED
duplicates, never submitted/registered. Stronger protected-single-child gap
remains useful: PROTECTED-BRACKETED-CHILD-ZERO.signature-v2/body-v3 (575lines)
predicts every-fuel/full zero in arbitrary raw positive-label history, from
ONE source child bracketed by selected old markers, chosenGlobal<=3 and
oppositeGlobal<=2. It uses the closed two-level exterior lemma for the removed
site. New main-based branch node/CtxBoundZeroOfProtectedBracketedChildAndOppositeUnitAxis,
registration160129-f5d181 DONE454.3s2326MiB, local cap restored exact20G.
Isolated161014-d7696e accepted11.4057s2100MiB; original161310-076303 CLOSED
8.486s672MiB/standard axioms/type lock intact. Commit162307-cd74d3 DONE,
SHA6d9fbdda82e2ab99fc7f8dff65c4c3b0f3d757dd.
It closes the raw single-protected-child obstruction; full ROOT-NF remains open.
Positive first-child singleton321line and arbitrary unmarked two-run593line
drafts are prepared UNREGISTERED/UNCHECKED. The latter reuses a raw
alternating-site=>3runs proof draft to rule out the extra right thread.
ROOT-NF.induction-v9.source.lean.txt is prepared UNINSTALLED/UNCHECKED,
1338lines/3holes, preserving full IH and exact statement and adding conditional
three-run source/NF zero coverage. Assembly ReferenceError logged/repaired
before any source/compiler action. ROOT-NF.AXIS-TWO-GAP-MAP.md records scope.

## Evidence and operational limitations

All artifacts are under runs/r18-sol-20261001. Failed compiler attempts and
probes were preserved and logged before repairs. The main branch contained19
malformed inherited lock metadata entries; strict recovery used original
accepted R15 provenance and asserted every inherited type_hash/type_pp
unchanged. Each node branch has a dedicated LOCK-REPAIR provenance receipt.
Temporary local registration caps were restored before final checks/commits.

The full index is stale; only authorized targeted extraction was used. The
systemd user bus is hidden in the sandbox, so guarded jobs are followed via
the external worker. A transient SQLite lock recovered without mutation.
Other jobs were only inspected read-only. No approval or verified callback.
The queue delayed our final check for65.9min, then advanced. Earlier admission snapshots
show sufficient resources under40G, while the held worker4531 started before
the30G->40G change. A cached30G primary-worker budget is a plausible cause of
the aged30G extraction blocking younger jobs; loaded runtime config is unverified.
Evidence and the persistent blocker are recorded in es log; no worker/config/DB
manipulation, cancellation or bypass was attempted. Resumed admission cause
remains unverified. Guarded branch-create160014-a7cdc4 failed a misplaced
--json passed to git; logged before correct retry160043-15aaa5 DONE. Inherited
metadata recovery and temporary8G registration cap are recorded for the new
protected-child branch; exact20G configuration restored after registration.
At20:29Z the1G commit remained queued behind another20G job. Snapshot shows
44.1GiB available,15G live caps,0leases/0worktree owners; fit under configured
40G does not establish loaded worker state. No intervention or causal claim.

Pending final work: finish authorized checks/proofs, concise final mathematical
handoff, separate code/library self-review window under the single-model rule,
usage sync/end and update this report. Research deadlineOct2 02:45:22.637741Z;
consolidation02:15:22.637741Z, finalization03:15:22.637741Z. Do not mark the
native goal complete early or convert an incomplete proof into theorem credit.
