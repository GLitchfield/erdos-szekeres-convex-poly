# Coordinator pending work (Claude, updated 2026-10-01 ~14:50Z)

Focus (Gavin, 01 Oct): all trials on C1r; multi_run's FLIP core is parked.

## Running Sol trials (all on C1r)

| Trial | Route | Host job | Worktree | Deadline |
|---|---|---|---|---|
| R16 | N_root via the N_ends selector | 20261001-010310-364fa1 | main-integration-20260928 | hard end 17:34Z |
| R17 | X (singleton-base exchange) | 20261001-095747-bca76e | sol-12h-20260913 | ~22:00Z |
| R18 | ROOT-NF (normal form implies C1r) | 20261001-104505-2e0e57 | sol-12h-20260916 | ~22:45Z |

## Local main is NOT pushed (32 R15 commits on top of 5847e155)

R15 integration (user-approved): 26 closed helpers, the open FLIP with its partial proof, and the
multi_run composition. Excluded: the singleton FLIP 7558a563 and b2f1ee9a.

To finish:
1. After R16 ends (quiet window), run a full extract: `es job run --mem 30G ... -- es extract`,
   about 12 min, which also builds the 28 new modules.
2. Commit "Refresh index".
3. Push and wait for CI.

R16's results also need merging after its run, with Gavin's OK; use the same procedure (union imports
and lock, take main's nodes.json and status.md, then the full extract).

## Coordinator probes

- X falsifier at k=7: job 20261001-100118-b9bc37 → runs/claude-x-sweep-20261001/x-k7.json.
- Saturation up to 6 runs, k up to 7: job 20261001-101259-fb4fea → runs/claude-n-selector-20261001/saturation.txt.

## Evidence so far

- N_ends: 62,876 contexts at k=5..8, 0 failures.
- Saturation (a,u >= 3, 2-4 runs): 0 variation.


## Update 2026-10-01 ~17:00 local (Claude)

**R16.** Ended. Its N_ends pieces are merged into local main (3f3fc51d, 4a990c3f). Its other
closed helpers (endpoint zero etc., used by R18) are on its worktree only.

**R17 / R18.** Running. R17 host job is 20261001-095747-bca76e; R18 host is
20261001-104505-2e0e57, with windows ending ~02:00Z and ~02:45Z.

**Blockers needing the user:**
- **es worker 4531 caches the 30G budget** (it started before c5dad861). An aged 30G job blocks
  the queue (cancelled my full extract 143930-072b2a). Restart the worker to apply 40G.
- **Local main harness/statements.lock is invalid JSON** since R15 commit 76a1b269: missing
  `  },` after line 910. `es status` and some node-validated `es job run` calls fail on local
  main. My hand repair was blocked by permission policy.
- **Full extract + "Refresh index" + push of local main** waits on both of the above.

**Research.** Research is in runs/claude-residue-20261001/NOTE.md:
- one-level structure explained (closed form = bound, profile/LIM);
- relaxations refuted;
- PEEL normal form proposed;
- splitting identity.

PEEL k=6 job 20261001-164842-fedeb6; PEEL-ENDS job 20261001-165459-f274b9.

## Correction ~19:00 local: the lock damage is 19 records, not one line

The one-line sed fix is insufficient: the file still fails at line 923.
- **Cause.** The R15 integration's union merge (mine) damaged 19 R15 records.
- **Repair (prepared, not installed).** runs/claude-coordinator-20261001/repair_main_lock.py
  produces statements.lock.repaired: 378 records, the 349 origin/main records identical, 19
  restored from their R15 commits, all type hashes unchanged. Report in LOCK-REPAIR.main.json.
- **To install (Gavin):**
  `cp runs/claude-coordinator-20261001/statements.lock.repaired harness/statements.lock`
- **Then:** commit "Repair statements.lock records damaged in the R15 integration", full extract
  (needs the 40G worker or a quiet machine), "Refresh index", push.

## Proposal (not implemented): harness DB lock contention

**Evidence.**
- The worker log is full of "database is locked".
- R18 logged a 16:07-16:17Z lock episode.
- My B1 cancellations needed retries.

**Cause** (tools/es/es/store.py, Store.__init__). Every es command WRITES on open:
- the `PRAGMA user_version` write probe;
- the SCHEMA script;
- `_migrate`;
- the FTS schema;
- `purge_expired_claims`.

Meanwhile the DB is in rollback-journal mode (`journal_mode=delete`), so readers and writers block
each other.

**Proposed change** (needs Gavin's OK; harness code):
1. `PRAGMA journal_mode=WAL`, set once and persistent in the file. Readers no longer block
   writers; only writer-writer contention remains. Check first that Codex's read-only sandbox
   opens still work under WAL: a read-only process needs existing -wal/-shm files. If not, keep
   the read-only fallback with `?mode=ro&immutable=1` for pure readers.
2. Make open cheap:
   - run SCHEMA/`_migrate` only when `user_version` is below the code's schema version;
   - drop the unconditional write probe, detecting read-only mode on the first real write instead;
   - move `purge_expired_claims` into the claim/ready/status commands.
3. Add a regression test where concurrent readers and one writer complete without "database is
   locked".


## Done 2026-10-01 23:07 local

- Lock repair committed (8c8b6d5b) after Gavin installed it.
- Worker restarted by Gavin (pid 1499252).
- Full extract (job 225253-883e9a), Refresh index (e3c87197), pushed 5847e155..e3c87197; CI
  36958650425 in progress.
- R17 and R18 reviewed (es log). Both Done(narrowing); X and C1r stay open; the same obstacle
  as everywhere else (two-level threading / sibling penalty).

**Open decisions for Gavin:**
1. Integrate the closed helpers from R16 (30), R17 (13) and R18 (13), using each trial's
   INTEGRATION manifest.
2. R19 on PEEL with the cost-based choice (runs/claude-residue-20261001/R19-BRIEF-DRAFT.md).
3. DB WAL proposal (above).
