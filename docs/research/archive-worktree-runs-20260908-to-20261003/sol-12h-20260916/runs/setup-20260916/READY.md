# Sol 12-hour checkout readiness

Status: **READY** as of 2026-09-16 13:20 America/New_York.

## Identity and tracked state

- Setup agent: `codex:01a0ab1b-a6b2-7ea1-b933-14356cc551e2`.
- Checkout: `/home/gavin/git/erdos-szekeres-convex-poly/runs/worktrees/sol-12h-20260916`.
- Branch: `node/CtxTwoMarkerYoungerExteriorInternalComplementCutComponentBounds`.
- HEAD: `52e48fa26bf60734fc6f5383f0a3348ec1ee6d74`.
- Cache source HEAD: `433d1b33305642aa65bf4dee3dcd12a00e77ed97`.
- Hashing all 10,494 tracked `*.lean`, toolchain and manifest files in both checkouts found
  zero mismatches. The extra destination commit is harness-only.
- Setup-side `git status --short` and `git diff --stat` were empty immediately after the targeted
  check and before handoff. The admitted native researcher then began its authorized theorem work;
  the later status shows its `ESBlueprint.lean` edit and new component module. Those changes do not
  belong to bootstrap.

## Build cache

The old `.lake/build` was physically copied; it was not symlinked or hard-linked to the source
worktree. The destination-only absolute root substitution remains a disclosed one-off bootstrap
operation and is not a promoted cache mechanism.

- Source and destination: 143,677,424,002 bytes and 145,854 regular files each.
- Destination: 10,545 `.olean` files and 10,548 `.trace` files.
- Source traces naming the old checkout: 709; destination traces retaining that root: zero.
- Regular-file device/inode intersections between source and destination: zero.
- Dependency packages use the normal `.lake/packages` symlink to the primary checkout.
- Detailed artifact: `runs/setup-20260916/cache-copy.txt`.

Guarded receipts, including failures and cancellation:

- `20260916-124853-1aed3e`: failed before copying because the fresh checkout lacked `.lake`.
- `20260916-124922-3b1247`: canceled after 54.1 seconds during the first physical copy when
  coordinator wording was clarified; its 9.6 GiB partial destination was retained and resumed.
- `20260916-125101-e0cb90`: copied the remaining cache in 1,497.0 seconds; exited 127 only after
  the copy because the worker PATH lacked `rg`. The completed tree was reconciled in place.
- `20260916-131625-85e15e`, `20260916-131638-85c157`,
  `20260916-131706-86969f`, and `20260916-131714-6db7ab`: short failed post-copy trace-search
  attempts. They did not recopy the tree; their exact inline commands and outcomes remain in the
  job journal.
- `20260916-131737-08712f` and `20260916-131744-a65e2f`: terminal successful post-copy
  isolation/trace validations. The latter was the native researcher's idempotent duplicate.

## Lean and harness evidence

Guarded targeted check `20260916-131802-18727d` compiled and extracted
`ErdosSzekeres.ctx_two_marker_internal_complement_cut_six_top_width_middle_residual_classification`
in the new checkout. It finished with exit code zero. Its result artifact is
`ba0cc7f4886fa79fef95502bafa6cbe6e1f36e93629643e8403609065fe36de9`:

- targeted build: 13.232 seconds, 2,107 MiB peak;
- `sorry = false`, statement lock valid;
- axioms: `propext`, `Classical.choice`, `Quot.sound`;
- no nonstandard axioms and no tag errors.

The bootstrap agent's duplicate targeted check `20260916-131814-1ef78d` was canceled while still
queued, so the module was not built twice.

Fresh `es status --json --full` after the check reports `stale = []`, `problems = []`, 251 closed,
11 open, one claimed and one refuted. The one claimed node reflects the admitted native research
run; `es ready` returned the remaining ready frontier. This setup intentionally reuses the existing
source-identity-keyed full index rather than claiming a newly regenerated full oracle.

The independent harness compatibility receipt is
`runs/sol-12h-20260916/harness-tests.txt`: 206 passed, one skipped in 213.05 seconds. Its
unexpectedly long unguarded duration is retained in the coordinator's setup review.

## Setup accounting

- Window: `window-12f261a9180d4100`, arm `setup`, status `complete`, accepted results: one.
- Post-close usage reconciliation: 9,801,711 input tokens, 9,664,128 cached input tokens, 32,411
  output tokens, and 9,345 reasoning-output tokens. The harness notes that final reporting after the
  snapshot may lag.
- Untracked setup created here: `.lake/packages`, `.lake/build`, and this
  `runs/setup-20260916/` receipt directory. Bootstrap changed no mathematical or other tracked
  source; subsequent tracked changes are owned by the admitted native research run.
