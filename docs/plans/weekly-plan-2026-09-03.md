# Weekly plan: 3–10 September 2026 (Week 1)

Governing documents: `research-plan-2026-09-03.md` and `review-2026-09-03.md`
in this directory.  This file is the Week-1 instance of the weekly plan the
research plan asks for.  It records what was settled on day one, what runs
overnight, and what is decided next.

## Settled on 3 September

| Item | Outcome | Evidence |
|---|---|---|
| Q1 email to Baek–Balko | Drafted, then decided not to send (4 Sept): no outside help on Theorem 8 | `docs/correspondence/2026-09-03-baek-balko-draft.md`, `workstream-b-self-reliant-plan.md` |
| Q2 Fin15 endpoint | True. The anchored instance is UNSAT in under 3 min on two solvers; the unanchored instance gave no verdict in 58 min | experiment 0110 |
| Q3 census at k = 5 | 30 of 77 pentagon-free 8-point types are decomposable in no sweep direction; all 77 have a top split in some direction | experiment 0107 |
| Q3 census at k = 6 | Exact (4 Sept): 68,696 of all 88,423 hexagon-free 9-point types (77.7%) are decomposable in no direction; 797 have no top-level split in any direction | experiment 0107 |
| Q4 constructions | All 24 extremal sets at k = 6, 7 have (k−1)-gon-free halves | experiment 0108 |
| Q10 conjecture | Refuted as stated: Theorem 19 sets at k = 7, 8 are decomposable in no direction | experiment 0108 |
| Stop generator and scheduler | The systemd user unit is disabled; no scheduler unit or process exists | `runs/agents/continuous-idea-generator/systemd/` keeps the unit file |
| Build hygiene (G) | Every Lean build now runs through `scripts/guarded_lake_build.sh` (cgroup memory cap, no swap, CPU quota) after the 3 September out-of-memory incident | `runs/experiments/20260903-week1/build/guard.log` |

## Workstream A: route change

The plan's A1–A2 (bridge to EmptyHexagonLean's external axiom) is replaced by a
certificate of the project's own, with no external axiom:

1. `AnchoredPresentation.lean` proves that every swept configuration can be
   re-indexed so that vertex 0 sees every later pair as a right turn, with
   strong polygon sets preserved (quarter turn, shear, Tóth–Valtr projective
   chart).  Compiles on standard axioms.
2. The anchored seventeen-point signotope instance (680 variables, 217,176
   clauses) is UNSAT in 5 min with proof logging; its dependency core has
   59,684 base clauses and 1.67 M additions, replayed in the kernel through 192
   checkpoint segments (experiment 0109).
3. `ES6Bridge.lean` turns the anchored conclusion into
   `ForcesConvexPolygon 6 17`, `ErdosSzekeresFormulaAt 6`, and the strong-six
   cardinality ceiling.  **Done 2026-09-04 03:50:** `ES6Certificate.lean`
   compiles; `forces_six` and `erdosSzekeresFormulaAt_six` depend only on
   `propext`, `Classical.choice`, `Quot.sound`.  Q5 is closed.
4. The same anchoring handles the Fin15 endpoint: `AnchoredFin15Consumer.lean`
   turns the anchored Fin15 refutation into the fifteen/sixteen middle
   producer, and `PredecessorHalfSix.lean` composes `PredecessorHalfSubsetAt 6`
   unconditionally.  **Done 2026-09-04 12:34** after the 256-segment replay;
   axiom audit in the experiment note.

## Overnight build, 3–4 September (what actually ran)

All jobs are memory-capped and sequenced by
`scripts/run_guarded_build_plan.py`; the plan files `plan-20260903*.json` and
`plan-20260904*.json` in `runs/experiments/20260903-week1/build/` record the
successive re-plans, `driver.log` the stages, `guard.log` one line per capped
job with peak memory and OOM count.

1. ES(6) checkpoint chain, segments 0–191 (`build_checkpoint_chain.sh`):
   5.4 h, 60–160 s and up to 17.7 GiB per segment, no OOM kill.  ES(6) clause
   chunks and semantic segments in batches of eight alongside it.
   `ES6AnchoredUnsat`, `ES6Anchored`, `ES6Certificate` built at 03:50; axiom
   audit clean at 04:19.
2. Two generator defects found and fixed during the run, both in
   `generate_fin15_anchored_lean.py`: the `fiveSubset` support facts (a
   512-way `simp_all` case split, hours per file and crashing compilers) now
   reduce `(E.powersetCard 5).val` by `rfl` and compile in seconds; the
   `every_eight_has_strong_five` clause lemmas close each of their 56 branches
   with one `absurd` instead of `simp_all`.  Segments 064–107 and chunks
   238–251 were regenerated (experiment 0110).
3. Measured footprints that reshaped the batches: Fin13 clause chunks 090–097
   need 15–21 GiB each (single, 22 GiB cap, 30 GiB fallback after the chain);
   Fin15 no-strong-six chunks 220–238 about 10 GiB each (pairs at 24 GiB).
4. Remaining sequence in `plan-20260904f.json`: Fin15 heavy and tail chunks,
   semantic segments, Fin13 chunks 091–097, `StrongPredecessorBaseSix`,
   `AnchoredFin15Consumer`, the 256-segment Fin15 chain (about 6 h),
   `Fin15Anchored`, `PredecessorHalfSix`.

## Decisions for Gavin

- ~~Send the Baek–Balko email~~ Decided 4 September: no email; Workstream B
  proceeds without the authors (`workstream-b-self-reliant-plan.md`).
- `.wslconfig`: reduce `memory` from 48 GB and `swap` from 16 GB so Windows
  keeps headroom; suggested 36 GB and 4 GB with gradual memory reclaim.
- Q10 is refuted as stated.  Decide whether to keep the weaker form (every
  extremal set has a top split in some direction; true on every case checked)
  as the conjecture, or drop the direction-based framing.

## Next actions (4–10 September)

- ES(6) is verified and recorded (README, map, note 0109).  Still to do when
  the Fin15 chain finishes: `#print axioms` on `predecessorHalfSubsetAt_six`,
  record it, run `make test`, and commit when Gavin asks.
- Experiment 0111 done (4 September): all three 64-point octagon-free sets
  have verified heptagon-free halves; the chain enumerator makes the
  perturbation search below feasible.
- Workstream E: the first falsifier ran (experiment 0113): 760 heptagon-free
  single-flip neighbours of the 19 extremal sets all have hexagon-free
  halves.  Remaining: write the conjecture with its parameter, consumer, and
  falsifier; extend the walks (longer, non-nearest lines) at negligible cost.
- Workstream C: the brief for Sol is drafted
  (`sol-brief-etv-parameter-5.md`); the opening computation at n = 6 is done
  (experiment 0112: exactly the conjectured 16).  Remaining: n = 7 with a
  Tseitin encoding, then hand over.
- Workstream B: self-reliant plan drafted (`workstream-b-self-reliant-plan.md`):
  exhaustive small decomposable worlds with per-vertex external cap/cup
  profiles, mechanical invariant search, paper proof of the boundary
  family, then one parameterized Lean theorem; internal note as fallback.

## Resource rules in force

- One heavy job at a time per stream; two streams at most (a checkpoint chain
  and a batch stream), each under its own cap, total caps below 36 GiB.
- No multi-hour run without explicit go-ahead.
- Solvers and large Python jobs run under `systemd-run --user --scope -p MemoryMax=…`.
