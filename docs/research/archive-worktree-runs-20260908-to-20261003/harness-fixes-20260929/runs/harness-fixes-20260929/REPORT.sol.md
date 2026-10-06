# R5 Sol report: harness and evidence fixes

Status: complete at the scheduled deadline; final suite and usage closure passed.

Agent: `codex:01a0eeae-200b-7a01-bf1a-6771559955f7`
Branch: `harness/fixes-20260929`
Base: `5d58845b`
Usage window: `window-fc60dd11877440b1`

## Outcome

All six priorities in `RESEARCH-BRIEF.md` are implemented and committed. The tracked
worktree is clean at `efced4db2c2dbca1d6cbe43decd8f0eb76d5a592`. No Lean theorem,
extraction, or proof credit is claimed by this run.

## Implementation commits, in order

1. `0a11ec7d61caf07430de149d4418a2bdf37faccb` — prevent concurrent `es worker`
   processes with a shared project `flock`; stale file contents do not block restart.
2. `eadbe965d94931057c121d94dc56490649c348c8` — replace per-module opened-date
   histories with one merge/rename-aware pass and preserve committed dates in the index.
3. `18c3486c51bcf6348ce8935cd6dcfcdb6e8d7a5c` — make actual indexed dependencies
   block readiness; add destination/open-root cones, index transitions, and deduplicated
   closure burn-down.
4. `e4cbdbe96467b93ede52e47813fd41183e68b3e4` — recover `MemoryPeak` and OOM
   outcome from a stopped systemd scope when the in-scope stats writer is absent.
5. `f2beae5dcf890d4f5c5fa163783d53551956896f` — add immutable repeatable
   `es log --attach` references and conflict-safe preservation of worktree `runs/...`
   files cited by release notes.
6. `cbfc4c2f824e29af1b37eafbb6551642245333a5` — add the memoized compiled
   context-bound semantics, existing-factory integration, catalog/example, and finite
   cross-language regression fixture.
7. `d967f6659a4163c2c6a034d04a65a16ced0fe184` — audit follow-up: make
   signed-64-bit overflow explicit, validate the ctypes boundary, and require a nonsymlink
   owner-only compiled-library cache.
8. `51277972dd54997d9f889c029672ec41a581058e` — update the harness design and
   automation operating guide for the R5 behavior.
9. `3dc338b3eaa68d466c6eccbb9b6d30dbad4a630d` — complete the existing evaluator
   interface with honest `cache_info`/`cache_clear` compatibility and a registered-probe
   integration regression.
10. `e9116e024b13bcf0ca4ef67570847260ffc18e6a` — document that Python
    `SIGALRM` cannot preempt an in-flight compiled evaluator call, so prototype probe
    shapes remain independently bounded.
11. `033b66569823f5ac60c0a68c5c45fdb35a93bc2f` — make configured Git access
    honor a linked worktree's metadata pointer, fixing the real-checkout opened-date
    history pass and every other `gitutil` consumer's branch selection.
12. `31de30e753147fbbbdfe7b9e6a48f1eff64aa8b4` — reject final-component
    symlinks as release-evidence destinations so identical current target bytes cannot
    masquerade as a durable primary-checkout copy.
13. `f55b9ee87643ccc192d3dc53404bb78e050dfdf8` — retain claimed
    consumer-free nodes as open root cones, keeping the coverage metric stable across
    transient claim leases.
14. `a0b00821fbe14bdbb45143e6b28b3cf39b5e3564` — align the operating
    documentation with the audited R5 edge cases and exercise the opened-date parser
    directly in a configured linked-worktree regression.
15. `509270c33a57e82dd8754e71c4c7c8bd0c4d31fc` — promote compact zero-maxima
    agreement and compiled witness-replay boundaries into the recurring regression suite.
16. `4fb01fcd9cbb312b36a4518414fa109b8b69f14f` — declare the compiled evaluator's
    public C entry point explicitly, satisfying the expanded strict-prototype gate.
17. `8b5a8414e54e56a4743060adafc2dedc33b7b69c` — pin the adjacent exact and
    overflowing central-binomial cases at the compiled signed-64 boundary.
18. `383c84974a81efddb769b0d2f32cbc3c8f29a356` — conclude a claimed or
    standalone terminal operation with exactly one attempt row, removing close/retire
    inflation from burn-down attempt counts.
19. `3a667547366f7fc09e12adc7405eb6900245695c` — preserve a distinct terminal
    attempt when an intermediate check already ended the attempt for a still-live claim.
20. `19c98873e0458ac06a9c026ed31f59d943135d2d` — reject symlink components in
    release-evidence destination parents and avoid redirected or silently skipped copies.
21. `dbb3610e27312844156e1acd3bb3023876fe7075` — pin the required end-cut result
    with a one-entry compiled memo table, guarding correctness under cache saturation.
22. `eff85cd084ca3278a8aa4a456c249026c1be1d9f` — align the design document with
    the tested rejection of symlinks in release-evidence destination parents as well as
    at the final component.
23. `7f0a447d68a7c71f3e2bfe9d35d43641dd5858f4` — guard the public compiled
    evaluator's accepted `maxima == NULL`, `depth == 0` case from zero-length C library
    calls whose null arguments are not portably defined.
24. `6d1be769e502dadeda1be5f704d5553f3396d0f4` — verify the project worker
    lock across real process boundaries: a child is refused while the parent holds it and
    succeeds immediately after release.
25. `360f063fcf1b8b570078364b7ef99f5b0834cf15` — an interim diagnostics commit
    force-added ignored run files; coordinator review rejected that packaging choice.
26. `41968a59c373ffc72957637fa8f4a1b3a56cec9e` — close the coordinator's
    required evidence gaps: non-blocking artifact fallback, absolute/worktree citation
    normalization, precise OOM journal matching, bounded cwd-relative attachments, copied
    modes, and filtered burn-down queries.
27. `c5c4fddd576e7d67d780d36bf81ef8e6185de9a4` — remove all 36 interim run
    files from the index while preserving the complete evidence bundle on disk; the final
    tree has no tracked `runs/harness-fixes-20260929` files.
28. `acc16b0168d879e4c967134793df0197de29ef95` — omit unavailable destination
    cones and compute burn-down once per full status response.
29. `8def83f9d220c34a6eea52e0c190ea088645f133` — pin arbitrary publication
    `OSError` fallback: bytes remain immutable evidence and the claim is still released.
30. `dd6a02d54336f59a1b732fa5a70b6419ce3430a4` — context-manage usage JSONL
    streams, removing the previously deferred destructor-time resource warnings.
31. `0d71ca6eadf268945611c825f8287e3958be1252` — journal extraction roots and
    admit only primary-checkout `index-status` transitions to shared burn-down.
32. `efced4db2c2dbca1d6cbe43decd8f0eb76d5a592` — directly exercise both the
    primary and linked-root transition tags.

## Checks and receipts

Each numbered fix had a focused test and a full harness suite before its commit:

| Priority | Focused job | Full-suite job | Full result |
| --- | --- | --- | --- |
| 1 | `20260929-154131-ee2656` | `20260929-154141-d9523b` | 283 passed, 1 skipped |
| 2 | `20260929-154600-0407bb` | `20260929-154610-77b2f4` | 285 passed, 1 skipped |
| 3 | `20260929-155134-0111b0` | `20260929-155200-31e4a1` | 289 passed, 1 skipped |
| 4 | `20260929-155728-65d608` | `20260929-155743-5625db` | 291 passed, 1 skipped |
| 5 | `20260929-160222-98dc13` | `20260929-160235-3efd9b` | 293 passed, 1 skipped |
| 6 | `20260929-162427-db97b1` | `20260929-162507-16fa41` | 294 passed, 1 skipped |

Priority 6 and its audit follow-up also have these receipts:

- runnable catalog example: `20260929-162453-f55819`, output `1`;
- strict C11 warning gates: `20260929-162853-1bf895` and
  `20260929-163242-91dab2`;
- post-review 2,100-context differential: `20260929-162858-818ab9`;
- hardening-focused tests: `20260929-163248-81c443`, 4 passed;
- hardening full suite: `20260929-163312-3a0757`, 296 passed, 1 skipped;
- documentation integration: `20260929-164016-56a463`, 27 passed;
- touched modules with `PYTHONHASHSEED=1`: `20260929-164133-928212`,
  113 passed, 1 skipped;
- GCC path-sensitive analyzer: `20260929-164345-130f93`, clean;
- extended cross-language campaign: `20260929-164602-1055cb`, 9,150
  additional comparisons, source `test_context_bound_campaign.py`;
- bounded exhaustive cross-language campaign: `20260929-180014-cbe0af`, all
  339,262 contexts matched in 1,210.67 seconds at 469 MiB peak across the four
  acceptance triples; source `test_context_bound_exhaustive.py` enumerates the
  exact depth/word/maxima domain and explicitly carries no Lean proof credit;
- deterministic four-`S` stress campaign: `20260929-183656-45890e`, all 2,000
  contexts matched across the four acceptance triples in 3 minutes at 272 MiB peak,
  including zero sibling maxima; source `test_context_bound_four_s.py`;
- zero-maxima campaign: `20260929-170229-404fe6`, 3,000 additional comparisons,
  source `test_context_bound_zero_maxima.py`;
- registered-probe failure/retry: `20260929-170311-1dd5a5` exposed the missing cache
  interface, `20260929-170359-a5a45d` passed both regressions, and full suite
  `20260929-170415-271775` passed 297 tests with 1 skip;
- compiled witness serialization/replay: `20260929-170635-252bd6`, expected target and
  control sums reproduced;
- timeout-boundary documentation: `20260929-170834-840712`, 27 passed;
- linked-worktree Git metadata: focused `20260929-171252-317b29`, 2 passed;
- real-checkout opened-date audit: `20260929-171302-007dad`, all 327 indexed modules
  resolved and both named stale cases reported `2026-09-07`;
- post-correction full suite: `20260929-171318-7b2de8`, 298 passed, 1 skipped;
- release-evidence symlink hardening: focused retry `20260929-171655-df010a` and
  full suite `20260929-171713-eaeb63`, 298 passed, 1 skipped;
- claimed-root cone stability: focused `20260929-172009-99751b`, 2 passed, and
  full suite `20260929-172021-6f1106`, 298 passed, 1 skipped;
- worktree integration/docs: focused `20260929-172318-b23f54`, 27 passed, and
  full suite `20260929-172330-c508e9`, 298 passed, 1 skipped;
- promoted compiled boundaries: focused `20260929-172549-734662`, 2 passed, and
  full suite `20260929-172602-f18c3f`, 298 passed, 1 skipped;
- concurrent cold-cache compilation: `20260929-172827-7bafb9`, eight simultaneous
  processes returned `1`, with one final shared object and no temporary libraries;
- expanded C warning gate: initial `20260929-173024-95bc19` found only the missing
  public prototype; retry `20260929-173048-885714` passed; focused compiled tests
  `20260929-173057-030d0a` passed 4 tests and full suite `20260929-173108-0e7c5b`
  passed 298 tests with 1 skip;
- exhaustive S-only threshold sweep: initial invalid diagnostic
  `20260929-173418-0d61a9`, corrected `20260929-173445-f2f000` passed 8,434 cases;
  promoted frontier `20260929-173507-063e29` passed and full suite
  `20260929-173517-c99a9c` passed 298 tests with 1 skip;
- single terminal-attempt accounting: focused `20260929-173820-b923e3`, 9 passed,
  and full suite `20260929-173838-58816a`, 299 passed, 1 skipped;
- checked-live-claim refinement: focused `20260929-174119-ff8de4`, 2 passed, and
  full suite `20260929-174135-864cb1`, 299 passed, 1 skipped;
- cross-environment full suite: `20260929-174348-dd0d69`, 299 passed, 1 skipped
  under Python development mode, randomized hash order, `LC_ALL=C`, and `TZ=UTC`;
- evidence parent-symlink hardening: focused `20260929-174612-076570` passed and
  full suite `20260929-174625-4dd090` passed 299 tests with 1 skip;
- R5 resource-clean gate: `20260929-174904-54a583`, 92 touched-subsystem tests
  passed with `ResourceWarning` as an error, fixed C/UTC locale, and hash seed 31337;
- final current-subsystem environment gate: `20260929-183040-3edbb5`, 124 passed
  and 1 skipped under the same controls; it reproduced only the documented pre-existing
  `usage.py:80` warning, wrapped at destructor time as `PytestUnraisableExceptionWarning`;
- tiny-memo differential: `20260929-175022-485497`, 6,000 comparisons at cache
  limits 1/2/3/7; promoted case `20260929-175100-cbc6c3` passed and full suite
  `20260929-175113-f91c41` passed 299 tests with 1 skip;
- evidence-symlink documentation alignment: focused `20260929-175615-cc153a`
  passed 28 tests and full suite `20260929-175631-49a32c` passed 299 tests with
  1 skip;
- null/zero-depth C boundary hardening: strict warning gate
  `20260929-182150-1d6a34`, focused `20260929-182202-83182b` (3 passed), and
  full suite `20260929-182220-9ab112` (299 passed, 1 skipped);
- cross-process worker-lock regression: focused `20260929-182615-b92255` passed
  and full suite `20260929-182627-888b22` passed 300 tests with 1 skip;
- ASan/UBSan build and 30,000-call campaign: `20260929-164755-529b0c` and
  `20260929-164806-ac985b`, no sanitizer output, source
  `context_bound_sanitize_driver.c`.
- Python development-mode resource audit: `20260929-170001-173ef3`, 113 passed,
  1 skipped; its formerly deferred `usage.py:80` warning is resolved by `dd6a02d5`.

Coordinator-review and consolidation receipts:

- required coordinator regressions: `20260929-202123-309b27` (4 passed) and full
  `20260929-202133-65c3c3` (300 passed, 1 skipped);
- status cone/query follow-up: `20260929-202450-991d55` (4 passed) and full
  `20260929-202503-c4663b` (301 passed, 1 skipped);
- publication failure and usable-edge receipts: `20260929-202742-2249d9` (2 passed)
  and full `20260929-202750-6e693e` (301 passed, 1 skipped);
- cross-environment audit before the resource fix: `20260929-202937-495bdd`, 301 passed,
  1 skipped, reproducing only the nine known `usage.py` destructor warnings;
- resource-leak closure: focused warnings-fatal `20260929-203404-676d88` (7 passed)
  and full warnings-fatal `20260929-203416-90e35a` (301 passed, 1 skipped, zero warnings);
- primary-only transition accounting: focused retry `20260929-203739-a63b63`, full
  warnings-fatal `20260929-203749-f98424` (301 passed, 1 skipped), and direct negative-root
  receipt `20260929-204011-a70f44`;
- whole-package bytecode compilation: `20260929-204057-09e6aa`, rc 0;
- Git object/reachability audit: `20260929-204116-8faca7`, rc 0;
- scheduled final branch-wide suite: `20260929-210957-47ed94`, 301 passed, 1 skipped,
  zero warnings in 49.02 seconds under Python development mode, `-W error`, hash seed 917,
  `LC_ALL=C`, and `TZ=UTC`.

Final branch-wide suite: passed as above.

## Meaningful failures and corrections

- `20260929-154106-a654f0`: priority 1 test lacked a test-only `os` import.
- `20260929-154535-f3ed4e`: control-character Git framing was destroyed by
  `splitlines`; replaced by a printable record prefix.
- `20260929-155107-ceb95e`: transition fixture already contained a legitimate
  proposed-to-open event; assertion narrowed to the unique open-to-closed transition.
- `20260929-155634-f70a3c`, `20260929-155700-ab8768`: OOM test mocks did not yet
  cover the new post-scope query (the first repair targeted a same-shaped wrong block).
- `20260929-160925-34d1eb`: an overlarge random context domain produced no first-test
  result after 878.2 seconds; it was cancelled through the harness and replaced by a
  bounded 2,100-case fixture plus separate stress/sanitizer campaigns.
- `20260929-162741-79625a`: strict ISO C rejected `__int128`; the binomial recurrence
  was replaced by a portable gcd-reduced checked implementation.
- `20260929-170311-1dd5a5`: low-level compiled calls worked, but the registered probe
  required `cache_info` and `cache_clear`; commit `3dc338b3` supplies the compatibility
  surface and records per-call C memoization honestly.
- `20260929-171125-52fdb4`: the first real-history diagnostic passed a string where the
  configuration API requires a `Path`; it failed before calling Git and was corrected.
- `20260929-171144-b90498`: the corrected diagnostic exposed that configured `.git-data`
  was being resolved beneath this linked worktree, so all 327 modules appeared
  uncommitted. Commit `033b6656` follows the worktree's authoritative `.git` pointer;
  the real-history retry and full suite passed.
- `20260929-171620-2c4048`: the first destination-symlink regression exposed that
  whole-path `resolve()` erased the final symlink before validation. The corrected code
  resolves only the containing directory and the focused retry passed.
- `20260929-173024-95bc19`: the expanded warning-as-error gate found that the exported
  ctypes symbol lacked a prior C prototype; commit `4fb01fcd` declares the exact API and
  the identical retry passed without conversion, sign, shadow, or prototype warnings.
- `20260929-173418-0d61a9`: the first threshold sweep selected invalid `k=1` for
  `(a,u)=(2,2)` and failed before that case reached C; using `max(3,a+u-3)` kept all
  triples inside the contract and the corrected 8,434-case sweep passed.
- `20260929-175956-dc7113`: the first exhaustive-campaign launch omitted the
  repository root from `PYTHONPATH` and failed during import before either evaluator
  ran; the unchanged source completed under corrected job `20260929-180014-cbe0af`.
- `20260929-201717-208608`: the first coordinator regression run exposed two test-only
  import mistakes; `20260929-201841-371c19` then failed before collection because the
  external worker has no generic `python` shim. The explicit repository interpreter reached
  the suite in `20260929-201919-3afb7d`, where the last failure showed that CLI `UsageError`
  is returned and printed rather than propagated. All three corrections were logged before
  green job `20260929-201954-6804a1`.
- `20260929-203714-ced59f`: production transition tagging and burn-down filtering ran,
  but the new assertion lacked a test-only `json` import; retry `20260929-203739-a63b63`
  passed unchanged production code.

The attempt-accounting audit also found the pre-existing `release` followed by
`record_attempt` pattern in close/retire; it was not a failed job, but it doubled one
terminal operation in the attempts table. Commit `383c8497` replaces that sequence with
one tested store operation.

The immediate model review then found that an intermediate `es check` can end a claim's
attempt without deleting the claim. Commit `3a667547` distinguishes that state and records
the later terminal operation instead of silently losing it.

Every failure and plan change was recorded in the shared journal before the next
substantive attempt.

## Usage accounting

The deadline sync reconciled its source snapshot with zero delta through
`2026-09-30T01:40:01.413Z`. Completed treatment window
`window-fc60dd11877440b1` contains 1,231 assigned responses: 180,919,143 input
tokens, 179,524,992 cached input tokens, 1,394,151 uncached input tokens, 474,822
output tokens, and 154,269 reasoning output tokens. The native goal service reports
1,863,252 total goal tokens over 21,599 seconds; these are different accounting surfaces
and should not be conflated.

The factual window handoff reports zero associated jobs because its resource query includes
only jobs linked through window-associated operations. This brief required ordinary
`es job run` submissions, so their measured worker receipts remain in the shared job journal
and are enumerated above but are not rolled into that window resource subtotal. Zero in that
field must not be read as zero worker use.

## Reviewer/deployment checklist and open risks

1. The running worker was deliberately not restarted. After landing, allow its next normal
   restart to load the singleton lock; do not start a second worker before then.
2. Run a post-merge full `es extract` to refresh formerly `uncommitted` opened dates and
   establish the new index transition baseline. No full extract was allowed in this trial.
   The current extractor does not emit usable destination-to-blueprint edges, so a full
   extract will not make destination cones meaningful; edge-free destinations are now omitted
   instead of displayed as 0/0 until the extractor contract is extended. Consumer-free
   open-root cones are usable now.
   Review this migration from the primary checkout or a linked worktree; both now select
   their own correct Git `HEAD` while sharing the configured metadata store.
3. Run normal CI/Lean gates after landing. This trial did not build Lean and made no Lean
   source changes.
4. OOM fallback coverage deterministically simulates a missing stats file and retained
   scope accounting. The trial did not induce a destructive live OOM; systemd versions that
   do not retain `MemoryPeak` can still recover the OOM outcome from the journal but may
   report peak zero.
5. The compiled evaluator is optional diagnostic arithmetic. It requires `cc`, retains
   zero-valued children, raises `OverflowError` beyond signed 64-bit results, changes no
   existing caller, and is not an equivalence certificate for Lean.
6. The committed random fixture uses bounded shapes (`S` count at most 3) for a fast full
   suite, plus the required four-`S` end-cut example. The run artifacts supply 9,150 wider
   random comparisons, 339,262 bounded exhaustive comparisons, 2,000 additional four-`S`
   comparisons, and 30,000 sanitizer calls without burdening every commit.
7. The registered probe's Python `SIGALRM` deadline is observed only after an in-flight
   ctypes C call returns. Keep compiled shapes bounded; a future production evaluator should
   add a C-internal deadline/cancellation contract before relying on per-case preemption.
8. Concurrent first use is covered by a bounded eight-process diagnostic rather than the
   routine suite; publication was atomic in that run, but this remains finite prototype
   evidence rather than a general cross-platform concurrency proof.
9. Release-evidence publication rejects both final and parent-path symlinks. This is
   intentionally stricter than following a symlink whose current target happens to be safe.
   Conflicting or unsafe destinations now preserve the worktree bytes as immutable artifacts
   and allow the release to conclude instead of leaving a claim to expire.
10. Worktree-local `index-status` events remain visible in the journal but no longer change
    shared burn-down; only events explicitly tagged as primary-checkout transitions count.

Safest next action: review this branch commit-by-commit, land it without restarting the
current worker mid-job, then perform the normal worker restart and one full extraction before
treating stale opened dates as migrated. Do not use destination cone counts until extraction
supports destination dependency edges.

## Scope compliance

No merge, push, rebase, primary-checkout file edit, worker restart/signal, full extraction,
Lean build, node claim, or delegation was performed. All compilers, test suites, and commands
over one minute ran as guarded jobs with caps at or below 2 GiB.
The primary `main` ref remained `5d58845b64c80c52f843290e31fa573398ebdd9f`; an unrelated
pre-existing primary-checkout `ESBlueprint.lean` modification was observed and left untouched.

The trial contract required only `gpt-5.6-sol` at `xhigh` and prohibited delegation, so no
separate Astra reviewer was invoked. This agent reviewed every run-local source before use
and again during handoff preparation; the C artifact additionally has strict-warning,
analyzer, sanitizer, randomized, threshold, cache-saturation, and bounded-exhaustive receipts.
