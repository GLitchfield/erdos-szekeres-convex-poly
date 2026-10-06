# R13 code review and library maintenance

Sol self-review, 2026-09-30. The configured model remains gpt-6.1-sol at
xhigh; no delegation or model change occurred. The coordinator subsequently
reviewed and accepted the STUCK outcome, five closed helpers and registered
X; host/FINISH-REQUEST.json records that review. This document records the
Sol code self-review, distinct from coordinator mathematical acceptance.

The immutable checkpoint inventory is
`bce2898d3986139b00598a2912b18d141a2cbe6f90ce4e825ff315e970531f54`
(`REVIEW.full-checkpoint.json`). It hashes 46 run scripts, five tracked-script
differences and 13 inline job commands. This inventory is evidence for review,
not a successful proof receipt. The subsequent static copy
`X-falsifier-reviewed.py` preserves the falsifier from commit
eb65ce22ba759254ff4db4a06a159c5e70bd6f78 for review.

The baseline-to-worktree inventory starts at e0092804, whereas all node
branches correctly start at main41cc0e4b. The three downstream additive /
uniform-separator module differences are inherited baseline differences;
`git diff main --` those modules is empty. They were not modified by R13.
The untracked exact-limit node, singleton library module, regression test and
fixture need explicit review in addition to that tracked-file inventory.

## Reviewed semantics

- Singleton probes enumerate every child position, both orientations and
  every legal complementary coupling. A positive part paired with a zero
  part remains eligible. The retained `child` transformation agrees with
  `harness.research.primitives.part`: excluded children become fresh level-1
  markers, old levels increment and the new maximum is prepended.
- X probes audit the explicit leaf threshold against the compiled evaluator,
  enumerate every adjacent doubled pair, and map p to p for p<=y or p-1
  otherwise. The deleted copy maps to the retained copy. Every old cut is
  compared with all orientations/couplings at the mapped new position.
  The tracked falsifier preserves all failure counts while limiting displayed
  witnesses; a passing sweep does not prove X or singleton attainment.
- General-context probes include the separately labelled end-cut-refutation
  fixture plus the declared exact-child bounded family. The first generator
  failure used a dictionary API on the list-valued run_index; preserved
  `attempt1` and the journal document that no cases were evaluated then.
  Later versions change child count, explicit sample offset or cache size;
  they preserve the candidate and do not impose a kill deadline.
- The all-placement probe covers 31 multi-run four-child placements, three
  occupied levels, all eight side patterns, six level orders and 64 maxima
  choices at (5,5,6). It resets its persistent cache per placement, reports
  progress and writes `complete=false` checkpoints before its terminal
  `complete=true` output. It continues after mathematical counterexamples.
- Minimum / maximum active-capacity scripts differ only in the stated
  selector, not evaluator semantics. Minimum selection is refuted. Maximum
  selection has finite positive evidence only. Fixed-leaf lifting compares
  legal inner cuts plus the outer complement with every root cut at the same
  p; it is refuted without refuting unrestricted singleton attainment.
- Lean body / wrapper files preserve exact hypotheses. Full C1r composition
  has BOTH N and X as hypotheses. The <=3-child wrapper discharges N with the
  closed small-arity theorem. Neither scratch wrapper is a registered full
  conditional from X alone. Imports from the refuted end-cut module use only
  independently closed helpers, never its refuted theorem.
- Inline job commands perform branch checkout, node registration, process
  observation or maintenance validation. Git commands disable automatic
  maintenance and use the worktree metadata. Registrations use the harness;
  no existing statement was changed. Failed shell/interpreter/compiler
  attempts are retained and logged. Short local transcription commands
  created scratch wrappers and receipt summaries; they grant no theorem
  credit and do not replace guarded compiler execution.

## Retained recurring algorithm

`harness/research/singleton_cuts.py` promotes only the repeatedly reused pure
singleton-cut enumeration, as `research.singleton-cuts`. It reuses the
catalogued context-part implementation and accepts an evaluator callback.
Execution, caching, budgets, progress and output storage remain with callers.
The API explicitly requires at least two children and integer k>=3, checks
exposed callback globals, preserves zero sums and propagates overflow.
Original run scripts and outputs are preserved.

The checked-in fixture `harness/research/examples/singleton-cuts-v1.json`
retains all 24 choices from `asymmetric-singleton-witness.json`, plus four
unit-axis zero choices. Tests check exact frozen values and couplings,
invalid domains, mismatched evaluator globals and error propagation. The
catalog entry includes precise semantics and a runnable cleanup-safe example.

Guarded validation: 20260930-192820-7a8919 passed all ten tests in the
singleton and catalog test files (`library-singleton-tests.log`). The first
system-python attempt 20260930-192147-d4b2cd lacked pytest; its failure log
is retained separately and establishes no behavior. Guarded example
20260930-192847-4fa726 exited rc=0 and printed all twelve choices
(`library-singleton-example.log`).

The capacity selectors, fixed-position lifting and family-specific generators
remain run artifacts: they are speculative or false one-off mathematics and
do not warrant a library API. No new generic workflow implementation was
introduced; `es run review`, proof capture/check, targeted node checks and
the guarded job workflow were reused.

## Accounting limitation

The native-host review attempted to reassign requests already recorded in
the explicit local research window and refused. Its zero host-window count
therefore means unavailable accounting. Preserve those assignments and use
`USAGE.review-sync.json` for the all-thread reconciled snapshot, plus the
two local window reports for the recorded research/review split. Active and
later requests can lag. No matched baseline or savings claim is available.

The library is committed as
8fd0a9b8efa3325f492cfb952f810ed9b1b200a4 (guarded193614-ca9a52),
with exactly six library/catalog/test files. Its inline shell command tests
the expected branch and empty staging area, stages explicit paths, checks
whitespace and commits the reviewed message. The exact-limit node follows
in separate commit95559e090ff7044040348aec1c00ac7094fbd6af through
es node commit; no unrelated falsifier receipt enters either commit.

Final immutable inventory:
38e2a2cdf1b70fcb3038667a06f1891a6817ce1caaf3733f3c220dfa75b345a8,
REVIEW.full-final.json. It records48artifact scripts,8tracked-script
differences and14inline commands; pending/unknown jobs and active R13
claims are all0. The two additional artifact files are the static reviewed
X falsifier copy and the exact accepted one-level candidate copy. The three
additional tracked sources are the accepted one-level module, singleton
library module and regression test. Hashes match the inspected/accepted
sources; no further mathematical or code trial was launched. The fresh
C1r diagnostic receipt remains excluded from the committed node/library files.
This is a Sol self-review record; it does not waive external mathematical
review or turn the inventory into theorem credit.

Finalization, 2026-10-01: coordinator acceptance is now recorded in
host/FINISH-REQUEST.json and host/agent-run.json, with research deadline
00:00:34.307053Z and hard stop 00:30:34.307053Z. The updated bounded review
REVIEW.finalization.json references immutable
7e3af45718ba52622650b827a08076f89e6728ff583511e8da7d103c3a7b1a34;
the code inventory is unchanged (48 artifact scripts, eight tracked script
differences, 14 inline commands), with no pending/unknown jobs or active
R13 claims. Finalization changed reports and accounting only. No new code,
research, compiler invocation or test was added. Main 7d9c2fed contains the
four integrated helpers and registered X; fifth helper 95559e09 is accepted
for coordinator integration. C1r remains open and the native goal paused.
