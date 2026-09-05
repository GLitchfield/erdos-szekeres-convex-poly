# Experiment 0109: the anchored ES(6) = 17 certificate

Date: 2026-09-03

Status: complete.  `ES6Certificate.lean` compiled on 2026-09-04 at 03:50 after
the 192-segment kernel replay; `#print axioms` on `forces_six`,
`erdosSzekeresFormulaAt_six`, and
`SweptConfiguration.exists_strong_six_of_seventeen_le` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Question

Research-plan Workstream A and Q5: is `ForcesConvexPolygon 6 17`, and hence
`ErdosSzekeresFormulaAt 6`, provable in the project's own sweep-coloring model
without importing EmptyHexagonLean's external axiom?  The obstacle was the size
of the unbroken seventeen-point signotope instance (680 triple variables,
217,056 clauses), which no solver settled in an hour.

## Predeclared gates

- The anchored instance must be UNSAT on two independent solvers; SAT would
  mean the anchoring lemma or the encoding is wrong (sixteen points must remain
  SAT).
- The dependency core and its LRAT must round-trip exactly (segment bytes sum
  to the core LRAT, final empty clause reached).
- Kernel replay must succeed under the memory guard with no `oom_kills`; a
  replay failure is a pipeline defect, not a mathematical result.
- Resource bound: one capped compiler at a time for the checkpoint chain.

## Inputs and provenance

- Git revision: `c74c737` (working tree; nothing committed).
- Producer: `scripts/generate_es6_anchored_sat.py` (SHA-256 `5fa47e7b63d15c81f31e8f4ac30e4a271c434a84a5e7ec26dfc40962e6bbe2a9`);
  anchored CNF SHA-256 `11fb188b998da55b7664e78aabf7ba2c202afe8e2df3a28a3e849798146c74c0` (verified against the constant in the script).
- Unanchored `n = 9, k = 5` output is byte-identical to `certificates/es5-signotope.cnf`
  (checked with `cmp`), so the clause stream is the one behind `forces_five`.
- Anchoring lemma: `ErdosSzekeres/AnchoredPresentation.lean`
  (`SweptConfiguration.exists_anchoredReindexing`, `forcesConvexPolygon_of_anchored`),
  standard axioms only.
- Core extractor: `scripts/extract_lrat_dependency_core.py` (SHA-256 `c70ece361e0654d37e5b26e5c65c0797be67ba5b159c10ffd35cb9bd4db8ff97`);
  core CNF SHA-256 `d060e01cf3f8ca0244a30f9ec7a3a031bfb2720b520b89359eb8cfa458cf6d01`.
- Checkpoint splitter: `scripts/split_lrat_checkpoints.py` (SHA-256 `1387a4846c0ef39be1442ad3c28fd966a1d89a1d3a29f13b1f45d719a285ad7a`),
  192 segments, bundle size 4096, compact final segment.
- Lean generator: `scripts/generate_es6_anchored_lean.py` (SHA-256 `963519fc0ed2ae7e51b75511c985e02d55d81f0a7dec32fd5e3896f9175f725c`).
- Solvers: CaDiCaL 2.1.2 (Lean toolchain) with `--lrat --no-binary`; Kissat (system).
- Build guard: `scripts/guarded_lake_build.sh` (SHA-256 `41bc6d500020b7ad541255a1e2fd78c898cdde0c66ff9a5f6e4062356f67e859`).

## Method

Variables are the 680 increasing triples of `Fin 17`; true means a left turn.
Clauses: the rank-three one-change law on every four vertices (19,040), every
strong coloring of every six-subset forbidden (198,016), and 120 unit clauses
forcing every triple through vertex 0 to a right turn (the anchor).
`AnchoredPresentation.lean` proves the anchor is a normalization: a quarter
turn about the leftmost point, a shear, and the Tóth–Valtr projective chart
make vertex 0 see every later pair as a right turn while strong polygon sets
are preserved up to an index bijection.  The refutation's dependency core is
extracted, renumbered densely, split into 192 LRAT segments with carry sets,
and replayed segment by segment with Mathlib's LRAT checker
(`lrat_checkpoint_segment`, `lrat_checkpoint_final_segment`); semantic clause
lemmas per core clause connect the propositional atoms to the coloring.

## Independent checks

- Sixteen points: the same encoding at `n = 16` is SAT in 0.42 s, as sharpness
  requires.
- The `n = 9, k = 5` instance reproduces the kernel-checked ES(5) certificate
  byte for byte.
- Two solvers agree on UNSAT for the anchored seventeen-point instance.
- Segment byte sizes sum to the core LRAT size (473,626,552 bytes); the
  splitter reports the final empty clause id 1,728,795.

## Results

| Instance | Solver | Wall time | Verdict |
|---|---|---|---|
| n = 16, k = 6 (no anchor) | CaDiCaL | 0.42 s | SAT |
| n = 17, k = 6, no anchor | CaDiCaL | 55 min (stopped) | none |
| n = 17, k = 6, no anchor | Kissat | 55 min (stopped) | none |
| n = 17, k = 6, anchored | Kissat | 4 min 39 s | UNSAT |
| n = 17, k = 6, anchored, LRAT | CaDiCaL | 5 min 06 s | UNSAT (777 MB proof) |

Dependency core: 59,684 of 217,176 clauses (14,559 one-change, 45,005
no-strong-six, 120 anchor), 1,669,111 additions, core LRAT 474 MB.  Kernel
replay at 192 segments (`runs/experiments/20260903-week1/build/guard.log`):
5.4 h of compiler time in total, 60–160 s per segment, peak 17.7 GiB, every
segment under a 20 GiB cgroup cap with zero OOM kills; the 467 clause chunks
build eight per 19 s batch and the 128 semantic segments eight per 100 s
batch.  The 768-segment split was measured at about 95 s per segment and
discarded as twice as slow overall.  `ES6AnchoredUnsat`, `ES6Anchored`, and
`ES6Certificate` built in under five minutes once the chain finished; the
axiom audit of the final theorems took 25 min.

## Interpretation

Kernel-checked theorem: every anchored one-change coloring on seventeen
vertices contains a strong six-set (`es6Anchored_of_oneChange`), hence through
the anchoring lemma every swept configuration on at least seventeen vertices
contains one, seventeen points in general position contain a convex hexagon
(`forces_six`), and with the classical sixteen-point construction the
happy-ending formula is exact at six (`erdosSzekeresFormulaAt_six`).  The
strong-six cardinality ceiling `strongSixCeiling_of_anchoredSeventeen` is the
named consumer for the fixed-six predecessor-half composition.  No claim is
made about the abstract (non-realizable) signotope tier at seventeen: the
anchor is only justified for sweep-realizable colorings.

## Reproduction

```console
python3 scripts/generate_es6_anchored_sat.py --output runs/experiments/20260903-week1/es6-signotope/es-17-6-sb.cnf
~/.elan/toolchains/leanprover--lean4---v4.29.1/bin/cadical --lrat --no-binary es-17-6-sb.cnf es-17-6-sb.lrat
python3 scripts/extract_lrat_dependency_core.py ...   # see core/extract.log
python3 scripts/split_lrat_checkpoints.py certificates/es6-anchored-checkpoints/core.cnf core/core.lrat certificates/es6-anchored-checkpoints --original-clauses 59684 --segments 192 --lean-prefix ES6AnchoredCheckpoint --lean-dir ErdosSzekeres --namespace ErdosSzekeres.ES6 --bundle-size 4096 --compact-final
python3 scripts/generate_es6_anchored_lean.py --segments 192
scripts/build_checkpoint_chain.sh ES6AnchoredCheckpointSegment 0 191 20G
python3 scripts/run_guarded_build_plan.py runs/experiments/20260903-week1/build/plan-20260903.json --guard-log ... --log ...
```
