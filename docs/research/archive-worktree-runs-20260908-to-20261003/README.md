# Archive: research write-ups from the removed worktrees (2026-09-08 to 2026-10-03)

On 2026-10-06 the old git worktrees under `runs/worktrees/` were removed after branch integration (Gavin approved).
This directory keeps the Markdown write-ups of every run that lived in them:

- the Sol runs R3–R20 and R24;
- the Codex lemma runs of 09-08 to 09-10;
- the harness-fix run.

R21–R26 are already in `docs/research/archive-2026-09-28-to-10-05/sol-r2*`.

- **Run data.** The full run data (3.4 GB: SAT outputs, receipts, JSON) is kept on local disk only, in the
  git-ignored `runs/archive-worktrees-20261006/`. It is not in git. Compiled Lean build caches (122 GB) were
  deleted; they are regenerable.
- **Deleted branches.** `deleted-branches-20261006.txt` lists the 220 local branches deleted that day, with tip
  SHAs.
  - 201 had all their content on main.
  - The 19 holding the only copy of some work are on GitHub as `archive/node/<name>`: open a=6 gate scaffolds,
    context-route scaffolds, the duplicate lemma, and one uncommitted R20 certificate committed as WIP.
