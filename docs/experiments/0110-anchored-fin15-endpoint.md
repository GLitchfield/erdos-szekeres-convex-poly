# Experiment 0110: the anchored Fin15 predecessor-half endpoint

Date: 2026-09-03

Status: complete.  `Fin15Anchored.lean` and `PredecessorHalfSix.lean`
compiled on 2026-09-04 at 12:34 after the 256-segment kernel replay (6.2 h,
87 s and at most 11.1 GiB per segment, no cap hits); the axiom audit of
`predecessorHalfSubsetAt_six` is recorded in the results below.

## Question

Research-plan Q2 and Workstream A step 3: does every sweep-realizable,
strong-six-free one-change coloring on fifteen vertices contain a
strong-five-free eight-set?  This is the fifteen/sixteen middle of the
fixed-six predecessor-half theorem (`PredecessorHalfSubsetAtSixMiddle`); its
truth value had never been established because the corrected 4,823-variable,
62,218-clause instance did not finish.

## Predeclared gates

- The anchored instance must be UNSAT on two solvers; SAT would refute the
  endpoint (a fifteen-point counterexample) or expose an encoding error.
- The anchored CNF must be the corrected Ticket 0098 formula plus exactly the 91
  anchor units (digest check against the recorded unanchored hash).
- Kernel replay must succeed under the memory guard.

## Inputs and provenance

- Git revision: `c74c737` (working tree).
- Producer: `scripts/generate_fin15_anchored_sat.py` (SHA-256 `c60312cc66c7eb3efb8348c1de5f20583ffb412ae6a14a300cb9cbfb0386e0a2`);
  unanchored digest `6a1ad5ff…835e63` matches the corrected instance; anchored
  CNF SHA-256 `cb5c9fae96b9dfdebcf838ec509ab53a8c4ac82d385a01470980319dd5451073`.
- Core CNF SHA-256 `78cca30290f095cff29a892ccb8f386e093962f5045c183f57a462760fa10d1c` (4,302 variables, 32,309 clauses).
- Splitter and Lean generator: `scripts/split_lrat_checkpoints.py`
  (SHA-256 `1387a4846c0ef39be1442ad3c28fd966a1d89a1d3a29f13b1f45d719a285ad7a`), `scripts/generate_fin15_anchored_lean.py`
  (SHA-256 `957b3c9b5c6dddaac55ad576c715aabdfabeab5cfec61660248b773e65f0ab1e`), 256 segments.
- Consumer: `ErdosSzekeres/AnchoredFin15Consumer.lean`
  (`predecessorHalfSubsetAtSixMiddle_of_anchoredFin15Endpoint`).
- Solvers as in experiment 0109.

## Method

Variables: 455 triple colors, 1,365 strong-quad atoms, 3,003 strong-five atoms.
Clauses: one-change on every four vertices, the corrected strong-quad
definition, strong-five as the conjunction of its five strong quads, no
strong six-set (over five atoms), every eight-set has a strong five-set, and
91 anchor units.  Unsatisfiability says every anchored strong-six-free
one-change coloring on fifteen vertices has a strong-five-free eight-set;
anchoring (experiment 0109) extends this to every sweep-realizable coloring,
and the consumer restricts a fifteen- or sixteen-point configuration to its
first fifteen vertices and maps the eight-set back.

## Independent checks

- Digest of the unanchored prefix equals the recorded corrected-formula hash.
- Two solvers agree on UNSAT; the unanchored instance is undecided after
  58 min on both.

## Results

| Instance | Solver | Wall time | Verdict |
|---|---|---|---|
| unanchored | CaDiCaL | 58 min (stopped) | none |
| unanchored | Kissat | 57 min (stopped) | none |
| anchored | CaDiCaL | 2 min 53 s | UNSAT |
| anchored | Kissat | 3 min 15 s | UNSAT |
| anchored, LRAT | CaDiCaL | 2 min 55 s | UNSAT (919 MB proof) |

Dependency core: 32,309 of 62,309 clauses, 803,363 additions, core LRAT
566 MB, final empty clause id 835,672.  Generated Lean: 253 clause chunks,
108 support segments (4,302 support facts), 128 semantic segments.

## Build notes (4 September)

- The first generated `fiveSubset` support facts (every 5-subset of an
  8-set is one of 56) used a 512-way case split closed by `simp_all`; segments
  064 onward took over two hours each and their compilers died.  They now
  state `(E.powersetCard 5).val = ↑[…]` by `rfl` with the 56 sets emitted in
  Lean's `sublistsLen` order, and compile in about 20 s per 40-fact file.
- The `every_eight_has_strong_five` clause lemmas closed 56 branches with
  `simp_all`; they now `obtain` the 56 negated atoms once and close each
  branch with `absurd`, 3 s per lemma file in isolation.
- The `no_strong_six` clause lemmas split four indices over six values
  (1,296 branches pruned by `omega`, survivors closed by `simp_all`) and
  needed 12–14 GiB each.  They now apply the hand-written
  `isStrongPolygonSet_of_forall_five` (`StrongPolygonSubsets.lean`: a set with
  at least five elements all of whose five-subsets are strong is strong) and
  enumerate the six five-subsets of the six-set by the same `rfl` trick:
  10 s and 1 GiB per 128-lemma chunk.
- Measured compiler footprints under the guard after the fixes: `strongSet_iff`
  support segments 2.2 GiB per batch of four; `fiveSubset` segments 4 GiB per
  pair; every clause chunk category about 1.2 GiB per batch of eight.

## Interpretation

Q2 is settled at the solver level: the Fin15 endpoint is true, so the
fixed-six predecessor-half theorem closes once the ES(6) ceiling and this
replay are kernel-checked (`PredecessorHalfSix.lean`).  The result is about
sweep-realizable colorings; nothing is claimed for abstract signotopes.

## Reproduction

```console
python3 scripts/generate_fin15_anchored_sat.py --output runs/experiments/20260903-week1/fin15-unlogged/formula-anchored.cnf
~/.elan/toolchains/leanprover--lean4---v4.29.1/bin/cadical --lrat --no-binary formula-anchored.cnf formula-anchored.lrat
python3 scripts/split_lrat_checkpoints.py certificates/fin15-anchored-checkpoints/core.cnf core/core.lrat certificates/fin15-anchored-checkpoints --original-clauses 32309 --segments 256 --lean-prefix Fin15AnchoredCheckpoint --lean-dir ErdosSzekeres --bundle-size 4096 --compact-final
python3 scripts/generate_fin15_anchored_lean.py --segments 256
```
