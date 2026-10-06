# R9 Sol report

The registered conditional C3 reduction is **closed and committed** as
`4cf96422ce0f5b6d99ad03d3eaa703c6333470f4`, through commit job
`20260930-092916-755d72` (rc=0). Branch:
`node/CtxBoundAdditiveSingleRunAlternatingOfRunContractionAndDeletion`.

The proof uses strong induction on run length, the closed n=2/n=3 bases, and
DelMono separator deletion followed by C1 tooth contraction for n≥4. R6's
Boolean painting, interval reconstruction, and base transport are reused.
Statement and docstring are byte-for-byte unchanged; C1 and DelMono remain
explicit hypotheses. The native goal remains active before its mandatory
time gate `2026-09-30T21:08:02.442541Z`.

Checks:

- Full-statement scratch `20260930-092305-f4b7af`: rc=0, 17.11s,
  `target-02.log`, standard axioms only.
- Targeted `es check` `20260930-092622-ee8406`: rc=0, node closed,
  sorry=false, no uncovered axioms, type hash `2f0a94ddbcb29ccf` unchanged;
  build 22.77s, whole job peak 2362 MiB. Immutable receipt
  `a5c33d421cad204e34c740c56f576815f14c19fed0906008e24ca39599d0f153`,
  copied to `CHECK-RECEIPT.json`. Targeted incremental extraction only.
- R6 consumer verification `20260930-093734-c64ab7`: rc=0, 10.00s,
  `consumption-inline.log`. R9 directly supplies R6's alternating hypothesis,
  yielding the arbitrary-keep conditional additivity example.
- Original/final declaration comparison and Git whitespace/scope checks pass.
  Working tree is clean; commit contains one module and two derived index files.

All accepted axiom lists are exactly `propext`, `Classical.choice`, `Quot.sound`.
No merge, push, primary-source or other statement edit, full extract, new trial,
or delegation. Failed compiles, cache probes, the unstarted cancelled queue
request, and all evidence are documented in `MATHEMATICAL-HANDOFF.md`.
Final code review is in `CODE-REVIEW.md`; searches are in `SEARCHES.md`.

Claim released as closed. The required `es release` automatically mirrored the
linked mathematical handoff into the primary checkout, in addition to shared
harness state; this was a harness side effect. No primary source or branch was
edited, and no manual primary-checkout write was made.

Open risks: C1 and DelMono themselves remain external mathematical obligations.
The host's automatic job inventory misses thread-id-attributed R9 jobs; use
the exact receipts here, with no zero-resource or savings inference.
Safest next action: coordinator review of this commit and later composition
with proved C1/DelMono. R9 performs no further research trial.

By 13:44 UTC all theorem/check/commit/report work is complete. Only the native
goal's fixed time gate is pending; host job `20260930-090758-d1f606` is live.
Final goal completion must be audited after the required instant, without
extending deadlines or resetting usage limits.
