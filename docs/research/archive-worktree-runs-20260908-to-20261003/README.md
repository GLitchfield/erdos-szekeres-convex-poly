# Archive: research write-ups from the removed worktrees (2026-09-08 to 2026-10-03)

On 2026-10-06 the old git worktrees under `runs/worktrees/` were removed after branch integration (Gavin approved).
This directory keeps the Markdown write-ups of every run that lived in them:

- the Sol runs R3–R20 and R24;
- the Codex lemma runs of 09-08 to 09-10;
- the harness-fix run.

R21–R26 are already in `docs/research/archive-2026-09-28-to-10-05/sol-r2*`.

- **Run data.** The small, irreplaceable part of the run data (scripts, Lean scratch, receipts, every result file
  under 1 MB) is in `data/archive/worktree-runs-20261006-small.tar.gz`, 21 MB.
  - The large regenerable outputs (about 3.2 GB) were deleted on 2026-10-06.
  - The compiled Lean build caches (122 GB) were deleted as well.
- **Deleted branches.** `deleted-branches-20261006.txt` lists the 220 local branches deleted that day, with tip
  SHAs.
  - 201 had all their content on main.
  - The 19 holding the only copy of some work are on GitHub as `archive/node/<name>`: open a=6 gate scaffolds,
    context-route scaffolds, the duplicate lemma, and one uncommitted R20 certificate committed as WIP.
