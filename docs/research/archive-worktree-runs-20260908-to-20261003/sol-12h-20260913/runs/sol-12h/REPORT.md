This report was reconstructed by Astra after the native Sol session hit its usage limit.

# Sol/xhigh trial and automation review

The planned twelve-hour trial ended early at the account usage limit after
4h24m44s of native Sol time. It did not provide a full twelve-hour measurement.
Ten new Lean theorems passed all five validation stages; all ten are now committed.
The original additive-sandwich obstruction remains open. The final compiled frontier
is 227 closed, 12 open, one refuted, with no stale or problem indicators.

## Verified results

- Native thread:01a09c8d-5d42-71e3-9703-93f8a0acd03e, gpt-5.6-sol/xhigh.
- Host job:20260913-165501-73c98a; native goal usageLimited at
  2026-09-14T01:19:50Z. Requested start2026-09-13T20:55:05Z,
  fixed research deadline2026-09-14T08:55:05Z. Neither deadline was changed.
- Nine theorems were committed before the limit. The tenth finish operation
  op-fa8c1d21c008454e completed afterward at01:26UTC. Astra later verified its
  unchanged source hash and completed only its local commit, a8fa8c55.
- verified-results.json records every theorem, operation, stage job, source hash,
  type hash and allowed axioms. Each operation succeeded; every current source
  matches its accepted receipt. Axioms are only propext, Classical.choice, Quot.sound.
- Results cover large-history/capacity-two reductions, four-capacity pruning,
  capacity-three exterior geometry and bounds, interval transport, and mixed-capacity
  marker separation. They are reusable intermediate results, not ten old obstructions
  closed. The parent ctx_bound_additive_sandwich_one_singleton_end remains open.
- The finite probes reused the registered Python evaluator. One found a witness
  against a stronger exploratory bound; negative runs timed out. None earns Lean
  proof, equivalence or refutation credit. The direct-layout calculation was canceled
  at1038.4s without a result. All129 Sol jobs are terminal:97 done,30 failed,2 killed.

No Astra mathematical guidance was given during research. One Astra infrastructure
intervention reconciled a stopped Git auto-maintenance scope without repeating the
commit. Sol's first roughly24minutes were spent repairing worker/cold-cache setup.
The coordinator's repeated status polling also consumed substantial tokens; this
cost is included, not credited as research progress.

## Recorded usage

| Role | Output | Uncached input | Cached input |
|---|---:|---:|---:|
| Astra setup | 217,698 | 971,651 | 35,306,112 |
| Sol setup helpers | 157,199 | 740,017 | 22,902,784 |
| Astra monitoring and initial recovery | 103,791 | 449,141 | 67,679,360 |
| Sol research | 327,816 | 1,923,145 | 146,491,392 |
| Sol host smoke | 9,310 | 46,924 | 969,728 |
| Astra post-run review (snapshot) | 21,853 | 227,857 | 4,241,408 |
| Sol worker-fix helper | 14,137 | 85,645 | 1,449,728 |
| Total snapshot | 851,804 | 4,444,380 | 279,040,512 |

All-in-usage.json preserves the separate reasoning-output subset; do not add it to
output again. Local source imports reconcile with recorded counters. Setup helper
lineage and gpt-5.6-sol/xhigh identity were verified from session metadata; whole
helper sessions include their requests before parent-window registration. Root
monitoring includes initial recovery before the post-review window was registered.
The active review/reporting snapshot can lag the final response. No raw conversations,
credentials, dollar estimates or account-level quota weights are used in this report.

At the common three-hour checkpoint, this run had six new checked results and
226522 Sol +82155 Astra output tokens. The earlier Astra-directed trial had seven
new results and329399 Sol +229109 Astra output tokens. These are different tasks,
with different setup and theorem sizes: they do not establish a causal productivity
or weekly-quota saving. Setup, smoke and maintenance must be amortized separately.
Use es usage compare only for matched, completed task/source/outcome windows; the
existing comparison gate rejects an unmatched savings claim. A full-duration result
and matched task samples remain outstanding.

## Library review and cleanup

The requested recurring review and library-first instructions are in AGENTS.md
and CLAUDE.md. Use `es lib search "TASK"`, then `es lib show ID`;20 source-validated
entries expose APIs, examples and semantic limits without importing scientific code.
The review includes saved artifacts, changed tracked scripts and inline job commands.

POST-RUN-REVIEW.md records reused/promoted/deferred decisions. The recurring worker
root/reservation/extraction-cap bug is fixed, Lake can resolve the standard elan shim
without a login PATH, and harness Git calls disable automatic background maintenance.
Node registration and job execution are now directly discoverable. The experimental
hardlink/trace cache copy was deliberately not promoted without a general identity
and invalidation contract. No new mathematical Python algorithm was needed.

All152 harness tests passed in11.70s (post-review-tests.xml), including the real
nested-command regression that failed on the wrong checkout before the patch.
Primary commit:f53aead1. Prepared research checkout:8ae570bb on
harness/sol-12h-post-review. The temporary absolute Lake config was removed.
Unrelated primary research edits were preserved; nothing was pushed or published.

## Pending work

The live worker smoke20260915-150031-180e5a remains queued. The sandbox cannot
connect to the systemd user bus. The earlier queued reload was canceled before
execution (20260915-145914-7654ac). From the primary checkout in a normal WSL shell,
start `tools/es/bin/es worker`; then inspect the existing smoke receipt and its output
before admitting more work. No replacement research host has been submitted.

27316s (7h35m16s) of the requested research duration remain. CONTINUATION.md preserves
that scope and the required recovery checks. A future segment must be labelled
separately and must not rewrite the original host's frozen deadlines. The overall
goal remains incomplete pending the live worker check and full-duration testing.
