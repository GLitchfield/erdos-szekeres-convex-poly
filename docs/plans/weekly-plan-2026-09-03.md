# Weekly plan: 3–10 September 2026 (Week 1)

Governing documents: `research-plan-2026-09-03.md` and `review-2026-09-03.md`
in this directory.  This file is the Week-1 instance of the weekly plan the
research plan asks for.  It records what was settled on day one, what runs
overnight, and what is decided next.

## Settled on 3 September

| Item | Outcome | Evidence |
|---|---|---|
| Q1 email to Baek–Balko | Drafted, then decided not to send (4 Sept): no outside help on Theorem 8 | `workstream-b-self-reliant-plan.md` |
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
- `.wslconfig`: decided 4 September to keep `memory=48GB` and `swap=16GB`
  and add `[experimental] autoMemoryReclaim=gradual` (WSL 2.7.12), effective
  after the next `wsl --shutdown`; `scripts/wsl_return_memory.sh` covers the
  interim.
- Q10 is refuted as stated.  Decide whether to keep the weaker form (every
  extremal set has a top split in some direction; true on every case checked)
  as the conjecture, or drop the direction-based framing.

## Next actions (4–10 September)

- ES(6) is verified and recorded (README, map, note 0109).  Commits 1–2 are
  on `main`.  Still open: the axiom audit of `predecessorHalfSubsetAt_six`
  cannot be run as one `#print axioms` (its proof terms span ~90 GB of
  private oleans against 47 GB of RAM and thrash forever); run it
  compositionally, the Fin15 middle producer (36 GB working set) and the
  base-six composition (~32 GB) each alone with a 44 GB cap, at a time when
  the Windows host is not short of memory (the run pins the VM at its
  ceiling; `scripts/wsl_return_memory.sh` hands cache back afterwards).
  Then commit 3 (Fin15 certificate), `make test`, and the root build.
- Experiment 0111 done (4 September): all three 64-point octagon-free sets
  have verified heptagon-free halves; the chain enumerator makes the
  perturbation search below feasible.
- Workstream E: the conjecture is written with its parameter, consumer
  (`sweepExactUpperAt_of_predecessorHalfSubset`) and ordered falsifiers in
  `predecessor-half-conjecture.md`; the first falsifier ran (experiment 0113,
  negative).  Next: Horton-type and double-chain sets at k = 7, the
  signotope-tier SAT instance at k = 7 for n ≤ 32, longer flip walks.
- Workstream C: the brief for Sol is drafted
  (`sol-brief-etv-parameter-5.md`); the opening computation at n = 6 is done
  (experiment 0112: exactly the conjectured 16).  Remaining: n = 7 with a
  Tseitin encoding, then hand over.
- Workstream B: self-reliant plan drafted (`workstream-b-self-reliant-plan.md`).
  Step 1 done (experiment 0114): the class enumerated exactly through nine
  vertices, thresholds tight everywhere, extremal profiles recorded.  Next:
  step 2, the mechanical search for a profile-carrying bound that is
  additive across splits.

## Reconciliation, 5 September

**Closed since the 4 September entry above.**

- Workstream A steps 1–4 are done: `forces_six`, `erdosSzekeresFormulaAt_six` and
  the unconditional `predecessorHalfSubsetAt_six` are kernel-checked theorems. The
  axiom audit that could not be run as one `#print axioms` is done by the harness's
  module-order scan (validated against `#print axioms` on six declarations where
  Lean finishes): the three standard axioms only. Commit 3 (Fin15 certificate) and
  the root build are on `main`; the ES(6) family now lives in namespace
  `ErdosSzekeres.ES6` (its encoding clashed with E3State466's).
- The `es` harness is live on `main` (`docs/harness-design.md`,
  `docs/harness-implementation-2026-09-04.md`). Project state, what is open,
  claimed, closed, and what depends on what, is derived from the compiled Lean
  environment: `harness/status.md` is the frontier, `es status` / `es ready` /
  `es claim` / `es node add` / `es check` / `es close` are the working commands,
  `CLAUDE.md` carries the rules, and the pre-commit hook enforces layering, the
  statement lock and the axiom allowlist. This supersedes the ledger, tickets,
  packets and the weekly reconciliation as a state record; the weekly note is
  written by `es note`, with a Judgment section left for a human.

**Frontier on 5 September** (`es status`): four open, ready nodes.

- A: `forcesConvexPolygon_of_sweepExactUpperAt` (sweep bound to the planar
  statement) and `sweepExactUpperAt_of_predecessorHalfSubset_all` (the
  `Nat.le_induction`). These are the last two A items from the plan.
- B: `decomposableStateUpper_all` (Theorem 8 for all parameters; check the
  degenerate a = 1 / u = 1 cases before proving).
- E: `predecessorHalfSubsetAt_all`, conjecture kind, falsifier
  `harness/falsifiers/predecessor_half_constructions.py` (passes at k = 6, 7).
- Statement approvals on all four lock entries are provisional ("fable"); Gavin
  confirms via the CODEOWNERS review.

**Next actions (5–10 September).**

- A: prove the two bridge nodes (`es claim`, then `es check`; they only need
  `DecompositionPrimeNormalization` and `StrongPredecessorBicoloring`).
- B: step 2 of `workstream-b-self-reliant-plan.md` as before; the node exists to
  receive the theorem.
- C: the `etv_cap_five` conjecture node waits for its falsifier
  (`etv_cap5_small_n.py`, n ≤ 6 from experiment 0112's encoding); write it, then
  `es node add --kind conjecture`. The n = 7 computation and the Sol brief are unchanged.
- D: the direction-census falsifier (Gavin) is what the D/F conjecture nodes wait on.
- E: next falsifiers as listed above (Horton-type and double-chain sets at k = 7,
  the signotope SAT instance at k = 7, longer flip walks); add each as a step of the
  existing falsifier script so `es falsify` records them.
- Build hygiene: hand-written modules in the import closure of a certificate family
  are frozen (`harness/encodings.txt`; `es layers` explains); new lemmas that would
  touch one go in a new module. The nightly timer (03:00) runs the guarded core
  build, the extract check and the audit.

**Still Gavin's decision:** Q10's weaker form (every extremal set has a top split
in some direction) as the conjecture, or dropping the direction framing.

## Resource rules in force

- One heavy job at a time per stream; two streams at most (a checkpoint chain
  and a batch stream), each under its own cap, total caps below 36 GiB.
- No multi-hour run without explicit go-ahead.
- Solvers and large Python jobs run under `systemd-run --user --scope -p MemoryMax=…`.

## 5 September, evening (items 1–4 of the frontier, approved by Gavin)

- A: both bridge nodes are proved and verified by `es check` (standard axioms
  only): `forcesConvexPolygon_of_sweepExactUpperAt` on branch
  `node/forcesConvexPolygon_of_sweepExactUpperAt` (71cc7a3) and
  `sweepExactUpperAt_of_predecessorHalfSubset_all` on
  `node/sweepExactUpperAt_of_predecessorHalfSubset_all` (f37745b); one node
  per branch, statements untouched, awaiting review and `es close`.  With both
  closed, `ErdosSzekeresConjecture`'s upper half reduces to
  `PredecessorHalfSubsetAt j` for all `j ≥ 4`.
- C: node `etvCapFive_all` added with falsifier `etv_cap5_small_n.py`
  (pass at `n = 5, 6`; 16136f4).  The Sol brief and the `n = 7` computation are
  unchanged.
- E: falsifiers 1, 2 and 4 of `predecessor-half-conjecture.md` run and
  negative; falsifier 3 implemented as a bounded counterexample-guided
  search; all four folded into the harness falsifier (experiment 0115).
  Horton sets and double chains cannot reach 25 heptagon-free points; the
  deep-below unions that can are decomposable.
- B: step 2, first level, done (experiment 0116): the exact description of
  what a child of a deep-below split sees of its sibling (longest cap or cup
  of the sibling, and the two gaps holding the sibling's first and last
  vertex), verified on every split through seven vertices, and the
  positional extremal tables at the `(4,4,5)`, `(4,5,5)`, `(5,5,5)`
  boundary.  Next: the two-sided state and its closure test.
- Harness notes: `es node add` and `es extract` refuse to start below 42 GiB
  available, so SAT jobs must be stopped first; `es falsify` runs scripts
  without a cgroup.
