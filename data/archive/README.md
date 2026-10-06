# data/archive

## worktree-runs-20261006-small.tar.gz (21 MB, sha256 prefix 9c152ee64dd84082)

**Origin.** The small, irreplaceable part of the run data from the 13 git worktrees removed on 2026-10-06 (Sol runs
R3–R26, the Codex lemma runs of 09-08..09-10, the harness-fix run).

**Contents.** 10,436 files, restored under `archive-worktrees-20261006/<worktree>/...`:
- all scripts (Python, C, shell);
- the Lean scratch files of the runs;
- all Markdown;
- the saved uncommitted config patches;
- every result file under 1 MB: proof-check receipts, summaries, checkpoints, fixtures.

**Deleted.** About 3.2 GB of large regenerable outputs, i.e. the roughly 290 files over 1 MB:
- enumeration dumps;
- SAT model records;
- compiled .olean files.

Their findings are recorded in the es journal (`docs/research/archive-2026-09-28-to-10-05/journal-log-entries.json.gz`)
and in the run write-ups (`docs/research/archive-*`).

Restore:

```console
tar -xzf data/archive/worktree-runs-20261006-small.tar.gz -C runs/
```
