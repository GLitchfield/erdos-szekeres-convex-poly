# R5 harness-fixes handoff

Complete after the scheduled final suite and deadline usage closure.

## Exact remaining obligation

No implementation item from `RESEARCH-BRIEF.md` or the coordinator review remains open.
The scheduled branch-wide harness suite passed, the treatment window is complete with six
accepted priority outcomes, and the native goal is complete. No in-branch work remains.

After merge, the operator must restart the worker normally and run one full extraction for
opened-date migration and the new index-transition baseline. Current extraction does not
emit usable destination-to-blueprint edges, so this will not populate destination cones;
edge-free destinations remain intentionally omitted.

## Accepted implementation evidence

- Commits and primary job receipts are enumerated in `REPORT.sol.md` and `PROGRESS.md`.
- Final full runtime suite: `20260929-210957-47ed94` (301 passed, 1 skipped,
  zero warnings under Python development mode with all warnings fatal).
- Ordering audit: `20260929-164133-928212` (113 passed, 1 skipped).
- Resource-warning-as-error audit: `20260929-174904-54a583` (92 R5-touched tests passed).
- Usage-stream resource closure: `20260929-203416-90e35a` (301 passed, 1 skipped,
  zero warnings with `-W error`); the earlier `usage.py:80` warning is resolved.
- Git integrity: `20260929-204116-8faca7` (`git fsck --full --no-dangling`, rc 0).
- C analyzer/differential/sanitizer artifacts:
  - `runs/harness-fixes-20260929/test_context_bound_campaign.py`
  - `runs/harness-fixes-20260929/tests/context-bound-campaign.xml`
  - `runs/harness-fixes-20260929/test_context_bound_zero_maxima.py`
  - `runs/harness-fixes-20260929/tests/context-bound-zero-maxima.xml`
  - `runs/harness-fixes-20260929/context_bound_sanitize_driver.c`
  - sanitizer compile/run jobs `20260929-164755-529b0c` and
    `20260929-164806-ac985b` (the generated binary is intentionally not committed)
  - `runs/harness-fixes-20260929/test_compiled_probe_integration.py`
  - `runs/harness-fixes-20260929/test_compiled_probe_replay.py`
  - `runs/harness-fixes-20260929/test_compiled_cache_concurrency.py`
  - `runs/harness-fixes-20260929/tests/compiled-cache-concurrency.xml`
  - `runs/harness-fixes-20260929/test_context_bound_threshold_sweep.py`
  - `runs/harness-fixes-20260929/tests/context-bound-threshold-sweep-retry.xml`
  - `runs/harness-fixes-20260929/test_context_bound_cache_limits.py`
  - `runs/harness-fixes-20260929/tests/context-bound-cache-limits.xml`
  - `runs/harness-fixes-20260929/test_context_bound_exhaustive.py`
  - `runs/harness-fixes-20260929/tests/context-bound-exhaustive-result.json`
  - `runs/harness-fixes-20260929/test_context_bound_four_s.py`
  - `runs/harness-fixes-20260929/tests/context-bound-four-s-result.json`

- Exhaustive finite differential receipt: `20260929-180014-cbe0af` matched all
  339,262 enumerated contexts (1,210.67 seconds, 469 MiB peak) over the exact domain
  documented in `test_context_bound_exhaustive.py`.
- Four-`S` finite differential receipt: `20260929-183656-45890e` matched all 2,000
  contexts (3 minutes, 272 MiB peak) across the same four acceptance triples.

These are engineering/finite diagnostic receipts. There are no accepted Lean theorems or
proof receipts in this run.

The explicit run contract allowed only `gpt-5.6-sol` at `xhigh` and prohibited delegation,
so the same agent performed the required review of run-local source rather than invoking a
separate Astra reviewer. The sources were reviewed before execution and during this handoff.

Usage window `window-fc60dd11877440b1` reconciles model responses, but its resource subtotal
shows zero jobs because ordinary `es job run` rows are not linked through a window-associated
operation. The exact guarded job IDs above and in `REPORT.sol.md` are the worker receipts;
the zero subtotal is a coverage limitation, not an assertion of zero compute.
At closure the window contains 1,231 assigned responses and 474,822 output tokens; the native
goal service separately reports 1,863,252 total goal tokens over 21,599 seconds.

## Failed approaches and failure modes

- The first compiled-evaluator corpus combined up to five `S` letters with three external
  letters and was unsuitable for the routine suite; it was cancelled after 878.2 seconds
  with no semantic result (`20260929-160925-34d1eb`).
- The first exhaustive-campaign launch omitted the repository root from `PYTHONPATH` and
  failed before evaluation (`20260929-175956-dc7113`); the corrected launch completed.
- GNU `__int128` passed ordinary compilation but failed the strict portable-C gate
  (`20260929-162741-79625a`); the checked gcd-reduced recurrence supersedes it.
- Earlier priority-specific fixture/mocking failures and their exact jobs are recorded in
  `PROGRESS.md`; none was silently retried.

## Reusable observations

- The one-pass opened-date parser must use a printable commit-record prefix because Python
  `splitlines` treats several control bytes as line boundaries.
- Worker-lock coverage includes a real child process, not only two file descriptions in the
  test runner: the child is refused during the live lock and succeeds after its release.
- Destination cones cannot currently be meaningful: extraction does not emit usable
  destination-to-blueprint dependency edges, so even a full extract cannot populate them.
  Edge-free destinations are omitted instead of displayed as 0/0. Consumer-free open-root
  cones remain meaningful, and old JSON safely defaults the added destination field to an
  empty list.
- A killed in-scope stats writer requires querying stopped-scope accounting only after
  teardown is acknowledged; otherwise a similarly named stale unit is not authoritative.
- Immutable release evidence is preflighted for conflicts before any copy, then published by
  same-directory hard link so existing different content is never replaced.
- The compiled recurrence is quick on bounded small contexts but some five-`S`/three-external
  shapes are expensive; keep routine fixtures bounded and use guarded stress campaigns.
- The recurring compiled fixture now contains an explicit zero-maxima case and a serialized
  compiled-witness replay; the larger zero-maxima and replay scripts remain run artifacts.
- The registered probe assumes every evaluator callable has `cache_info` and `cache_clear`;
  the compiled wrapper now reports top-level calls while correctly declaring no persistent
  entries because its recursive memo table is rebuilt per call.
- A relative configured `git_dir` is not worktree metadata: linked worktrees must follow
  their `.git` pointer or they either see no repository or the primary checkout's `HEAD`.
  Real-checkout audit `20260929-171302-007dad` resolved all 327 indexed opened dates after
  this correction.
- Evidence publication must inspect the unresolved final destination component: resolving
  the complete path first turns a mutable symlink into its target and defeats the durability
  check. Commit `31de30e7` resolves only the parent and rejects final symlinks.
- Commit `19c98873` extends that invariant to every existing destination-parent component.
  The coordinator follow-up preserves unsafe/conflicting bytes in the immutable artifact
  store and releases the claim; it never follows the redirect or overwrites primary content.
- Absolute worktree citations and `runs/worktrees/<name>/runs/...` citations normalize to
  the worktree-local `runs/...` source. Publication `OSError` follows the same artifact
  fallback, and safe copies retain the source permission bits.
- Root cones are lifecycle metrics: a transient claim changes an open node's rendered status
  to `claimed` but must not make a consumer-free root disappear. Commit `f55b9ee8` covers both
  open and claimed root states.
- A terminal command must either finish its existing claim attempt or record one standalone
  attempt, not call both operations sequentially; `Store.conclude_attempt` now enforces this
  for close and retire. If an intermediate check already ended the claimed attempt, the later
  terminal operation remains a separate attempt rather than being lost.
- Shared burn-down counts index transitions only when extraction recorded the primary
  checkout root. Linked-worktree transitions remain auditable journal events without
  changing global closure counts; legacy untagged transitions are conservatively ignored.

## Unresolved questions and risks

- No deliberately destructive live OOM validated the host systemd retention behavior.
- No full extraction or Lean build was permitted, so post-merge migration/CI remains required.
- Finite Python/C agreement and sanitizer cleanliness confer no Lean proof credit.
- The existing worker has not loaded the singleton-lock code yet.
- Python `SIGALRM` cannot preempt a pure in-flight compiled evaluation; the current prototype
  needs bounded shapes until an internal C deadline/cancellation contract is added.
- Eight simultaneous cold-cache compilers published one loadable library in diagnostic
  `20260929-172827-7bafb9`; this finite race check was deliberately not added to every suite.
- The C source passes the expanded warning gate (`-Wconversion`, `-Wsign-conversion`,
  `-Wshadow`, strict/missing prototypes, all as errors) in `20260929-173048-885714`.
- The S-only threshold matched exact arithmetic or raised on overflow across 8,434 cases;
  the recurring suite pins `C(66,33)` as exact and adjacent `C(68,34)` as overflowing.
- Memo limits 1/2/3/7 matched Python across 6,000 bounded cases; the routine fixture pins
  the required end-cut result with `cache_size=1` so saturation cannot change semantics.
- The public C entry point accepts `maxima == NULL` exactly at depth zero. Commit
  `7f0a447d` guards all maxima copies/comparisons so that contract does not depend on
  implementation-specific behavior for zero-length C library calls with null pointers.
