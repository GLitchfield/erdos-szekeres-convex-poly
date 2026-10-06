# R15 incremental code and proof packaging self-review, 2026-10-01 06:23Z

Configured Sol at xhigh reviewed this work in separate window
window-1c772cdbd5f248ed. No delegation or Astra review is claimed. Earlier
complete reviews are CODE-REVIEW.interim.md and CODE-REVIEW.0603.md.

The newly changed probe_eight_family.py was read in full. Optional --depth4
constructs72 retained candidates:24 each globals7/7/7,5/7/7,7/5/7, with
four physical doubled runs, permuted occupied levels1..4, both sides and mixed
maxima1..3. Default64-triple family remains unchanged; deriving keep from child
indices2/3/6/7 agrees with its former fixed keep. The separate source snapshot
is retained. Candidate construction makes no bound assertion.

It reuses probe_eight_missing_cuts.candidates and the shared part/C evaluator.
Each positive row offers1600 lower candidates:4 maximal length-two segments,
10 legal outer d/orientations,4 proper3-of6 interval blocks and10 inner
d/orientations. Old parts have4children; flipped small has2; each inner leaf
has3. The bounded evaluator asserts at most4children per query and uses fresh
case-specific C factories, cold row memos and source hashes. No exact6child
right value is calculated. The six-child context may be the canonical keep
or its complement; the outer orientation stays associated with canonical keep.

Timing3861f1 preceded fullfbfc3b. All72 retained rows completed in42.962s,
with4865 candidates actually tested and one canonical keep of size2. Missing
lower certificates would return an inconclusive diagnostic even with rc0;
we inspected the full output and counted72 positive witnesses. Progress is
per row and every16 candidates; the total now uses len(rows), including72.

The first JS structural audit incorrectly required canonical right keep6 and
failed before writing output. It was logged, then corrected to verify exact
XOR and choose the six-child side by size. The completed audit verifies all
72 unique domains, maximal segments, proper inner blocks, legal couplings and
reported arithmetic. It does not independently evaluate C or prove FLIP.
Original data and source were not changed by this correction.

Portable Eight source e1b9dbe462472995134eec23374629297b0ff4d334fe5497fe05633d71d318e9
matches its archived clean candidate. The only change from the earlier accepted
source removed264 exact research IO pairs. A fresh full targeted check55bf5a
accepted the unchanged locked type8df31f7cd295f110, closed/no sorry/standard
axioms only. All326976 receipt bytes were fetched in5 pages; direct auxiliaries
are summarized by count rather than printed. Source contains no progress IO.
Final proof commit4a89613dacc11245c862898fbf7636b70da07f69 includes only the
node module and generated index/status files. An initial mistaken search-hit
sentence was corrected by guarded commit-message amendment6435ad; proof tree
was unchanged. The CutUpper overlay remains excluded and has its own commit.

Inline work reviewed: receipt pagination/field validation, hash comparisons,
diagnostic structural audit and its correction, cgroup reads/checkpoint review,
guarded metadata amendment and usage-window diagnosis. Inherited ES_WINDOW_ID
overlaps explicit windows, so supported usage sync --window selects the exact
phase instead of overwriting associations.

Inventory4fc3797dca9dcf77862e7c64f98634f97ca5511ca9300051adf10a414a28a841
was fetched completely:17 artifact scripts/22 tracked files relative to the
host's baseline, including other-agent main integrations. These are not22
changes made by R15. Native inventory usage/inline-command/proof coverage is
unavailable; actual receipts and explicit usage sync supply separate evidence.

Shared part, compiled evaluator and maximal-segment algorithms were reused.
No new generic implementation or promotion is warranted: the new candidate
family is one-off mathematics and the existing shared contracts fit execution.
The certificate liveness algorithm remains deferred pending another independent
certificate caller and a validated generic contract. No saving claim is made
from timings or inventory counts. The general positive FLIP is still open.
