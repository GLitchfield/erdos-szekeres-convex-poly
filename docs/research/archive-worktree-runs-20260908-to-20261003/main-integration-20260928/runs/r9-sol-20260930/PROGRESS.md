# R9 progress

2026-09-30 13:10 UTC: startup complete. Fixed reduction node claimed by
`codex:01a0f26d-e09b-7080-9c4e-2bf4a8d1ab7c`; research window
`window-1729ff967c6d4641` (host window `window-94c7d5b3a7644586`).
Branch is `node/CtxBoundAdditiveSingleRunAlternatingOfRunContractionAndDeletion`,
baseline `b706beec9cebb538179cd5ef8994d94c8a1d25a7`, clean at startup.

Harness status is current at c53fb41da463 / 2026-09-30T13:06:42Z; no stale warning.
Full `es status` has the recorded historical-release parsing bug;
`es status --brief --full` works. No extract, primary checkout edit, or delegation.

13:19 UTC: scratch shortening compiles (job `20260930-091803-0dd131`, rc=0).
For each side and admissible maximum, the alternating n+4-child part has bound
at most the corresponding n+2-child part: delete a false separator with DelMono,
then contract the resulting two true teeth with C1. Context/maxima equality uses
R6's glue. Both Boolean start values are checked. This is a local scratch helper,
not closure credit for the registered node.

13:22 UTC: strong-induction helper passed as `20260930-092105-0ec2df` (rc=0,
15.34s). First induction compile `20260930-091940-8e153f` failed only at
associative addition normalization of the n=3 sandwich endpoint; repaired.
13:24 UTC: full registered statement passed guarded scratch compile
`20260930-092305-f4b7af` (rc=0, 17.11s), axioms exactly `propext`,
`Classical.choice`, `Quot.sound`. Target-01 failed only at final parity/complement
simplification; Target-02 fixed both. Original and candidate theorem-header text
compares byte-for-byte equal. Complete proof/imports installed in the node module.
Next: inspect targeted check, commit with `es node commit`, and document receipts.
Native goal remains active until its user-set research deadline, even if closure
and verification finish early.

13:26 UTC: generic async targeted-check job `20260930-092404-84d216` reserved
20G and could not fit alongside shared jobs. It was cancelled while queued
(no started_at or pid, no compile begun) and replaced with a guarded 6G `es job
run` invoking the same `es check --targeted`. No mathematical coverage dropped.

13:44 UTC: R9 is closed and committed as
`4cf96422ce0f5b6d99ad03d3eaa703c6333470f4`; targeted check
`20260930-092622-ee8406` and commit `20260930-092916-755d72` both rc=0.
Consumer verification `20260930-093734-c64ab7` also passes. Standard axioms only,
same type hash `2f0a94ddbcb29ccf`, declaration/docstring unchanged, tree clean.
Mathematical handoff, report, and code review are written. No further R9 trial.

Native goal is intentionally still active under the explicit deadline rule;
only the time gate remains. Host job `20260930-090758-d1f606` is live. All R9
compiler/check/commit jobs are terminal. On any resume, inspect these receipts
and the latest host status before the deadline/consolidation audit.

14:38 UTC checkpoint: host `20260930-090758-d1f606` is verified running;
fixed deadlines and configured Sol/xhigh unchanged. HEAD is still
`4cf96422ce0f5b6d99ad03d3eaa703c6333470f4`, tree clean, proof source SHA256
`d464169b569714eb5245d77355230db49f88f4c037fb6e7b90428b53c8dfa36e` unchanged.
Host review recorded: leave it running; remaining ~6h30 is the user time gate.
No research/compile is pending and no trial is restarted.

Jobs so far: baseline `20260930-091036-e68c6b` rc=0; R6 helpers
`20260930-091123-25e15a` rc=0; parity/isolation
`20260930-091301-d536b3` rc=1 (two decide-coercion errors, fixed);
isolated parity `20260930-091520-b0efeb` rc=0; deletion/contraction helpers
`20260930-091633-9c87fa` rc=0; shortening `20260930-091803-0dd131` rc=0.
All logs and source snapshots are in this directory. Target fixture:
`4c336653e42d4f57745bce8f9da5e05a4b775d82e65d23c3efe6399a42e69eff`.

Research deadline: 2026-09-30T21:08:02.442541Z; consolidation begins 20:38:02Z.
