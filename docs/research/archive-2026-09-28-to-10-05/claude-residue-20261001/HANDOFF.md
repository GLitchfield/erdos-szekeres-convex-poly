# Research handoff: deque normal form for the context bound (Claude, 2026-10-01)

> **CORRECTION 2026-10-01 20:05 local:** EXTREME-PEEL2 (and END-PEEL) are REFUTED at k=6 on three-level contexts (non-degenerate, e.g. SSS1L3L2LS mx (1,1,1): bound 8, only the middle child of the run attains it; job 20261001-191322-86bf03). PEEL (singleton attainment, any child) survives and should replace EXTREME-PEEL as the organizing conjecture. See NOTE.md "CORRECTION".


Details and evidence are in `NOTE.md` (same directory). All results are diagnostic (compiled
evaluator); none is Lean-certified.

## Open obligation

C1r (via N_root + X) and multi_run (via FLIP) remain open. The proposed replacement organizing
conjecture is **EXTREME-PEEL2**: for a,u >= 4, >= 2 runs and bound >= 2, the bound is attained by
peeling the first or the last child. Its proof needs:
- FLANK-SWAP (exact; formalizable like MERGE);
- the splitting identity (exact arithmetic);
- three local lemmas: (A) reroute at an extreme with a rescue, (B) a single-run block, (C) an
  interface move.

The threading-limited rescue in (A) and the 4% residue of (C) are the unproved mathematical core.

## Established today (diagnostic)

- **One-level roots.** Bound = the depth-one closed form, which was derived from E tables. The
  bound is a function of the limit profile (type path <= 3), which explains C1r and saturation.
- **Parts of one-level roots.** Bound is a function of the profile, outside the limit-<=1
  degeneracy.
- **Refuted.**
  - LIM in general (dead runs).
  - Bilateral/MERGE closure, plain part bounds.
  - END- and EXTREME-PEEL at a=3/u=3.
  - EXTREME-PEEL on bound-1 three-level contexts.
- **Holding at a,u >= 4.** PEEL, END-PEEL and EXTREME-PEEL hold on two-level contexts (k=5);
  EXTREME-PEEL holds on three-level contexts with bound >= 2. PEEL also holds at k=6 so far.
- **FLANK-SWAP.** Exact on all non-skipped cases (12,672 same-side, 19,008 different-side).
- **Reroute anatomy.**
  - (A) works directly in 175,612 instances; 12,532 failures, all rescued by another extreme move.
  - (C) boundary move holds in 13,360 of 13,896 instances.

## Failed approaches and why

- **Residue colorings:** tight only at the root.
- **MERGE/plain relaxations:** they discard nested two-level threading, which optimal cuts use.
- **Pure limit-profile invariance:** dead runs make the bound exceed E.

## Running at handoff time

- PEEL at k=6 (two-level): job 20261001-165930-b61766.
- EXTREME-PEEL, three-level (a,u) shards: job 20261001-170928-cc14a5.
- EXTREME-PEEL, 5-6 children: shards 20261001-174251-969f94, -08c7ae; 20261001-174252-c980aa,
  -81ac39.

## Infrastructure blockers for the user

- Local main `harness/statements.lock` is missing `  },` after line 910 (R15 commit 76a1b269).
- `es worker` 4531 runs with the old 30G budget; restart it to apply 40G.

## Scripts

- `runs/claude-labels-20261001/`: peel_nf.py (modes all/ends/extreme, multi-level family),
  flank_swap.py, reroute_rescue.py, peel3_fail.py, rescue_classes.py.
- `runs/claude-residue-20261001/`: closed_form_check.py, lim_test.py, part_lim.py,
  bilateral_exact.py, plain_parts.py, anatomy.py.

## Late addition

A rescue-free induction candidate (RR + smallest-extreme-part GOOD-CUT) holds on a small family;
see NOTE.md "Late update". Scale-up is pending a free queue: R17/R18 run until ~02:00/02:45Z, and
the stale worker budget limits concurrency.
