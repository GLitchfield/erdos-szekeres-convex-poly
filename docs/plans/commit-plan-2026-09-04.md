# Commit plan for the 3–4 September work

Prepared 4 September 2026; approved the same afternoon.  Commits 1 and 2
landed on `main` as `f8467b7` and `72599c7` (fast-forward from Sol's merged
line at `c74c737`, no branch kept); commit 3 follows the axiom audit.  The
email draft and the review text were held back as proposed; the full
9-point census is committed gzipped.  The rest of this file is the plan as
approved.  All sizes are on-disk; git compresses the LRAT
text by roughly three to four times.

## Convention already in the repository

The repository tracks its certificates and generated modules: 1,544 generated
`ClauseChunk`/`CheckpointSegment`/`SemanticSegment` modules and 1.0 GB under
`certificates/` are in git today, including the 769-file
`predecessor-half-fin13-checkpoints` and `e3-state566-checkpoints` directories.
`runs/` is ignored, so solver outputs and raw LRAT traces are not tracked; the
committed checkpoint segments are the kernel-checked form of the proof.
No git LFS is configured.  The local `.git-data` is 532 MB.

## What is new

| Category | Files | Size | Notes |
|---|---|---|---|
| Hand-written Lean | 7 | < 1 MB | `AnchoredPresentation`, `ES6Bridge`, `ES6Certificate`, `AnchoredFin15Consumer`, `PredecessorHalfSix`, `StrongPolygonSubsets`, root import edits |
| Scripts | 9 | < 1 MB | two SAT generators, two Lean generators, census and construction scripts, guard, chain, plan driver |
| Docs | 8 | 0.5 MB | experiments 0107–0110, research-log rows, plans, correspondence draft, README and map edits |
| Data | 8 | 74 MB | census, construction, ETV, and flip-search JSON; the full 9-point census file alone is 67 MB (88,423 compact records) and may be better committed gzipped or as summary plus per-type table |
| Generated semantic modules | 1,091 | 267 MB | `ES6Anchored*` and `Fin15Anchored*` chunks, segments, support, encoding, final modules |
| Generated checkpoint modules | 450 | 3 MB | `*CheckpointContext`, `*CheckpointSegment*` |
| Certificates | 2 directories | 1,359 MB | 448 files (661 MB) for ES(6), 773 files (702 MB) for Fin15: `core.cnf`, base ids, segments, carry manifests, metadata |

Largest single file: `core.cnf` at 4.4 MB.  Every file is far below GitHub's
100 MB limit; the concern is aggregate size and clone time.

## Proposed commits

1. **Sources: anchoring, ES(6) bridge and certificate, Fin15 consumer,
   experiments 0107–0110.**  Hand-written Lean, scripts, docs, data, and the
   README, research-log, map, and root-import edits.  This commit is
   reviewable by a person.  Note two items inside it that Gavin may want to
   hold back: `docs/correspondence/2026-09-03-baek-balko-draft.md` (an unsent
   email to named people) and `docs/plans/review-2026-09-03.md` (the review
   text, if it was not meant for the public repository).
2. **Generated ES(6) anchored certificate: 192 checkpoint segments, 467
   clause chunks, 128 semantic segments.**  `ErdosSzekeres/ES6Anchored*` and
   `certificates/es6-anchored-checkpoints/`.  Reproducible from commit 1 by
   the commands in experiment 0109.
3. **Generated Fin15 anchored certificate: 256 checkpoint segments, 253
   clause chunks, 108 support segments, 128 semantic segments.**
   `ErdosSzekeres/Fin15Anchored*` and
   `certificates/fin15-anchored-checkpoints/`.  Only after `PredecessorHalfSix`
   builds and its axioms are audited.

Before any of them: `make test` under a guarded scope (it builds the library
root, which now imports every new module) and a confirmation that
`git status` shows nothing outside these categories.  Known pre-existing
failure (4 September): the three `test_build_orchard_xor_panel` tests error
with `source binding differs: ErdosSzekeres/StrongPredecessorBicoloring.lean`;
that file is unmodified and identical to HEAD, so the builder's recorded
hash is stale from an earlier commit.  Not touched here; decide whether to
refresh the binding in a separate commit.

## The size question

Following the existing convention adds about 1.6 GB on disk, perhaps
500–700 MB packed, to a repository whose history is already half a gigabyte.
Three ways to handle it, in order of preference:

- **Commit everything now (recommended).**  Consistent with the Fin13 and E3
  precedents, keeps `lake build` self-contained, and the research plan's
  Workstream G already schedules the structural fix: splitting the generated
  certificate modules into separately built Lake packages with cached oleans.
  That split is where the size belongs, not in an ad-hoc exception here.
- **Git LFS for `certificates/**/segment-*.lrat` and `carry-*`.**  Cuts the
  packed history by about 1 GB but changes the clone workflow for everyone
  and would leave the older certificates inconsistent unless migrated too.
- **Release artifact.**  Commit sources and generated Lean, publish the two
  certificate directories as a tagged release asset with SHA-256 manifests
  (`metadata.json` already records per-segment hashes).  The build would then
  need a fetch step, which the repository does not have today.

## Not for git

`runs/experiments/20260903-week1/` (3.7 GB, ignored) holds the raw solver
outputs, the 777 MB and 919 MB LRAT traces, and the build logs.  Keep them
locally until the certificates are committed and `make test` passes on a
clean checkout; then they can go.
