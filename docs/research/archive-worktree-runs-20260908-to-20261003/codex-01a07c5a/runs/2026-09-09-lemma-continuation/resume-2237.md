# Continuation at 2026-09-09 22:37 UTC

The user-authorized 12-hour goal is ACTIVE, with no token budget. Fixed start2026-09-09T19:32:21Z and deadline2026-09-10T07:32:21Z (3:32 a.m. EDT). Do not reset the timer or complete the goal before the deadline and final checked handoff. The quiet foreground worker started by the user is working; do not ask them to restart it. Continue autonomously, including immediate authorized commits and pushes. No parallel proof agents.

ROOT=/home/gavin/git/erdos-szekeres-convex-poly
WT=ROOT/runs/worktrees/codex-01a07c5a
OUT=ROOT/runs/2026-09-09-lemma-continuation
ES_AGENT=codex:01a087a7-d0cf-7e23-8514-e295400a06ee. Use OUT/es wrapper; it supplies environment. Git in WT: git --git-dir=.git-data --work-tree=.; preserve inherited modified harness/config.toml and root main/other agents' files. Root AGENTS/restart doc and Lean skill read earlier.

Every >1-minute command goes through es job run. Use OUT/submit.py; proof/build/targeted check3G, full refresh28G serialized with other Lean jobs, publication2G; shared budget30G. Full refresh helper restores config from28G to3G. Targeted checks MUST say `check NODE --targeted --budget10`, with no extra positional `node`; run_es.py guards this after the earlier dispatch incident. Never run bare large lake builds. Statements only registered/restated through harness. Search before drafts, ready/claim before formal work. One node per branch, header preserved byte-for-byte. Commentary at least every60sec.

## Formal progress and current job

Eleven theorem PROOF commits are checked and pushed. All eleven also have verified, pushed full-index commits. Manifest run.json is authoritative for all hashes and job IDs. Baseline114 closed; latest refreshed environment125 closed,11 open,1 parent claim,1 refuted; stale=[] and problems=[].

11: ctx_active_boundary_marker_rank_pair_union_bound, stem active-boundary-pair.
-592 lines, compiled FIRST TRY in21.3868sec,760MiB.
-Build20260909-182352-19cd12.
-Targeted check20260909-182554-102805 passed locked statement, no sorry, standard axioms only.
-Type hash650dc71f1105d4e9.
-Proof publish20260909-182812-4d4aa1 passed; commit a252375883f9d8e9e2cf84014d82c777f6fe320b.
-Full refresh20260909-182845-344a11 passed; tree hash31902d9994ad039e;138 nodes; no problems. Actual child scope peak about5.2GiB, no OOM/cap events.
-**CURRENT INDEX PUBLICATION20260909-183526-71ea2a**, output active-boundary-pair-refresh-published.json, cap2G, started22:35:26Z. At22:36:38 still pending. Poll and inspect. Do not repeat proof publication or refresh.
-Current branch node/ctx_active_boundary_marker_rank_pair_union_bound; its node claim was released closed after proof publication. Parent ctx_bound_additive_sandwich_one_singleton_end remains claimed OPEN.

After index publication, set chain-one-straddling-spec.json expected_head to the actual full index commit. Fresh ready already saved proofs/ready-before-chain-one-straddling.json;10 open ready nodes reviewed. Selection rationale logged under parent. Register next candidate with register_node.py, apply_body.py only after successful registration, build, targeted audit, immediate proof push, full refresh, index push.

## Prepared sequence, all searched, unregistered and uncompiled after11

12.chain-one-straddling, ctx_chain_one_straddling_unique_axis_level,18lines. Geometry with two child witnesses straddling an actual marker and chosen pure chain≤1: every actual chosen marker is the same level between witnesses. Removes global/k/capacity assumptions using auxiliary globals4 and suitably largek.
13.two-boundary-upper, ctx_two_boundary_marker_upper_normalize,397lines. All children/younger markers between two positions of one level; truncate before it, chosen min(G-2,k-M), endpoint/fuel/full monotonicity.
14.two-boundary-erase, ctx_two_boundary_marker_erase_normalize,455lines. Same double decrease, oldest chosen level, erases only that level and retains older opposite history.
15.chain-one-two-level, ctx_chain_one_children_exterior_of_two_levels,35lines. Pure-chain≤1 children all in a common exterior of two actual chosen levels; no global/k/activity assumptions.
16.active-two-boundary-rank, ctx_active_two_boundary_marker_rank_union_bound,604lines. Active children/younger chosen markers bracketed at one indexed level; min(G-2,k-M)≤3; exact opposite rank union, inactive children arbitrary, older opposite history retained.
17.separating-marker-normalize, ctx_separating_marker_erase_normalize,**814lines latest**. Selected marker separates all children and younger chosen positions from all older chosen positions. Erase only it, lower selectedG by1, samek; export child positions, depth−1, surviving indexed-level ext/side/maximum, opposite pure-trace equality, **positive labels**, every endpoint/fuel/full comparison. NO k-M cap: that stronger normalization is false. Generator prepare_separating_normalize.py and novel helper separator-greedy-fragment.txt. Both need updating consistently if later debugging. Added positivity by reusing old active-boundary hErasePositive. All uncompiled.
18.NEW separating-retained-rank, ctx_separating_marker_retained_boundary_rank_union_bound,**125lines**. All source children active, separator hypotheses from17, chosenG≤5, a specified older actual boundary marker and explicit boundary condition on all surviving younger chosen positions. Normalize then apply existing linear boundary theorem; unchanged opposite ranks give exact source rank-union charge. Generator prepare_separating_retained_rank.py. This is exterior control, not full square. Search proofs/separating-retained-rank-search.json. Potential future tactic issues only; no Lean test yet.
19.NEW triple-face-interval, rank_triple_face_interval_union_card_sq,**76lines**. Exact cardinality of two endpoint-anchored ordered-triple faces for intervalI: each face size choose(w+1,2), intersectionw, unionw², includingemptyintervals. Generator prepare_triple_face_interval.py. Search proofs/triple-face-interval-search.json. Pure finite counting, no context inequality assumed. Uncompiled.

Each has signature/body/description/pr-body/spec files. Set expected_head only from the actual preceding full-index publication; expected branches already chained. Imports for17 include old erasure helpers;18 imports17/old active boundary;19 imports18/old binomial count helper.

## New diagnostic evidence this turn (NOT formal progress)

- own-zone-path-probe.json, job20260909-182312-a76925:445contexts,328 completedlow/55 completedhigh,62timeouts, no low/high/geometryfailure. Refined low candidate z*w minus occupied adjacent zone edges01,12; disconnected02 gets2w, adjacentpair2w−1, allthree3w−2. High candidate choose(w+1,2)+far_exterior_indicator*(w−1). No opposite history in this family. Both unproved.
- chosen-five-small-face-probe.json, job20260909-182755-f37038:922completed,906positive,545with somechosenC3,356allactivechosenC3,185nonuniformrankintervals,78timeouts; no square/triple-facefailure. Smaller2–4childcontexts,mixedchosen/oppositehistory,unindexedmarkers. Seed2026090921,58.49sec. Diagnostic only.
- Preserve earlier FALSE low z*(w−1)+1 witness own-zone-charge-probe.json: SS E1.lower E2.lower E1.lower S,max[3,0],a7,u5,k9,width6,allchosenlimits2,zones02,bound12>11. Whole-source cut own-zone-counterexample-cut.json:own12,companionmax0..4gives16,total28<36;coupledmax5gives9,total21. Directsourceboundtimedout5sec. Rejection affects the standalone low charge only.
- Preserve separating-marker-stronger-rejection.json: S E1.lower E2.lower,max[4,0],a6,u5,k6,originalbound1; erase1andGminus1gives5; additionallycapchosenbyk-Mgives0. Hence17mustNOTassertthatcap.

Research notes higher-capacity-square-route.md updated. Two new cautions: run-group decomposition uses FULL group bounds, so a same-fuel mutual induction with full triple-face potential is circular without a separate argument; child-count induction may avoid it. Also, a merged pivot group can contain mixed chosen capacities, so a uniform-square theorem requiring all sourcechosenC3 does not automatically imply the full face potential. Both are open proof obligations. No general square/face/context parent theorem is claimed.

## Worker, awake, timer, final requirements

Awake job20260909-153542-ad824c live; Windows request confirmed; heartbeat22:32:56Z, windows_exit_code:null. Linux logind inhibitor denied earlier, already recorded. Bootidca967a75-a19a-45df-bbd0-58a14b1e2600. Awake fallback ends08:32:21Z. Only create OUT/stop-awake AFTER final checked handoff; leave user's worker running.

02h checkpoint completed21:32:29Z (20260909-173224-5006eb). **Next23:32:21Z label04h**, then01:32,03:32,05:32,07:32. Run checkpoint.py through submit.py256M at due time, avoid manifest publication mutation overlap. Do not repeat02h or resettimer.

At07:32:21Z stop new research, release parent claim BEFORE a lengthy final audit (its TTL is shortly afterdeadline), finish safe checks/publications, verify all pushes/index/standardaxioms, release remainingclaims, write checked finalhandoff, stop awakeprocess, then markgoalcomplete. No tokenbudget report required. Nevermarkcomplete justbecauseaturn/contextends; automatic active-goal continuations are working.

## Latest update at22:39:45 UTC — supersedes old current-job notes

Eleventh index publication20260909-183526-71ea2a PASSED all extract/layers/audit/status checks and pushed commit20482203b3e50bcc3720410299659dab01744513.

Twelfth registration20260909-183734-3a87eb PASSED in102.1sec. Node ctx_chain_one_straddling_unique_axis_level is claimed until06:39Z; current branch node/ctx_chain_one_straddling_unique_axis_level. Its18-line body is applied with unchanged header. **CURRENT BUILD20260909-183945-b1cc83**, cap3G, output chain-one-straddling-build-1.json. Poll this build next, then targeted check, immediate proof push, full refresh, index push. Statement hash3d07f1b5bade1583. Eleventh fully verified pre-registration state was125closed with no stale modules/problems; new12 means the index will temporarily be stale only for that pending node.

## Latest update at22:40:06 UTC — immediate next action

Twelfth first build20260909-183945-b1cc83 PASSED in3.2826sec,561MiB. **CURRENT TARGETED AUDIT20260909-184006-ce651b**, cap3G, output chain-one-straddling-check.json. Poll it next. If locked statement/no sorry/standard axioms pass, immediately publish_node.py chain-one-straddling under2G, then refresh_after_node.py under28G, then publish_node_refresh.py under2G. Do not repeat registration/build. Current count:11 fully checked/pushed proof+index results, twelfth compiled and auditing. Goal remainsactive, nextcheckpoint23:32:21Z.
