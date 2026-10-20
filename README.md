# Erdős–Szekeres convex polygons in Lean 4

The Erdős–Szekeres "happy ending" conjecture says that every set of
`2^(n-2) + 1` points in the plane in general position contains `n` points in
convex position, and that no smaller number works. It is known only for
`n ≤ 6`. This repository formalizes the problem in Lean 4 with mathlib and
works toward the general case.

A result counts here only when its exact statement has a compiling Lean proof
that uses no axioms beyond Lean's standard three (`propext`,
`Classical.choice`, `Quot.sound`).

**Status:** active research. The general conjecture is open.

## Results

Every theorem below compiles in the `ESCore` library and passes the axiom
audit, with no `sorry` and no non-standard axioms (see the Destinations table
in [`harness/status.md`](harness/status.md)). The definitions they rest on
(general position, convex position, `ForcesConvexPolygon`,
`ErdosSzekeresConjecture`) are in
[`ErdosSzekeres/Basic.lean`](ErdosSzekeres/Basic.lean).

| Result | Lean theorem | Source | Prior work |
| --- | --- | --- | --- |
| `ES(3) = 3`, `ES(4) = 5` | `erdosSzekeresFormulaAt_three`, `erdosSzekeresFormulaAt_four` | [`SmallCases.lean`](ErdosSzekeres/SmallCases.lean) | classical |
| `ES(5) = 9` | `erdosSzekeresFormulaAt_five` | [`ES5Certificate.lean`](ErdosSzekeres/ES5Certificate.lean) | classical |
| `ES(6) = 17` | `forces_six`, `erdosSzekeresFormulaAt_six` | [`ES6Certificate.lean`](ErdosSzekeres/ES6Certificate.lean), [experiment 0109](docs/experiments/0109-anchored-es6-certificate.md) | Szekeres–Peters 2006; see below |
| `2^(n-2)` points with no convex `n`-gon, for every `n ≥ 3` | `classical_lower_sharpness` | [`Extremal.lean`](ErdosSzekeres/Extremal.lean) | Erdős–Szekeres 1961 |
| Upper bound `C(2n-5, n-2) + 2` | `tothValtr_upper` | [`TothValtrUpper.lean`](ErdosSzekeres/TothValtrUpper.lean) | Tóth–Valtr 1998 |
| Upper bound `2^(n + 32·√(n·⌈log₂ n⌉) + 128)` | `hmpt_explicit_upper` | [`HMPTExplicitUpper.lean`](ErdosSzekeres/HMPTExplicitUpper.lean) | Holmsen–Mojarrad–Pach–Tardos 2020 |
| Upper bound `2^(n + 64·⌈n^(1/3)⌉²·⌈log₂ 3n⌉ + 128)` for `n ≥ 65` | `suk_explicit_upper` | [`SukPositiveFractionExplicitUpper.lean`](ErdosSzekeres/SukPositiveFractionExplicitUpper.lean) | Suk 2017 |
| The predecessor-half property at every level implies the conjecture | `erdosSzekeresConjecture_of_predecessorHalfSubsetAt_all` | [`Closed/A/…AtAll.lean`](ErdosSzekeres/Closed/A/ErdosSzekeresConjectureOfPredecessorHalfSubsetAtAll.lean) | this project; see below |
| The predecessor-half property at level 6 | `predecessorHalfSubsetAt_six` | [`PredecessorHalfSix.lean`](ErdosSzekeres/PredecessorHalfSix.lean), [experiment 0110](docs/experiments/0110-anchored-fin15-endpoint.md) | this project |
| The exact bound at `k = 6` in the abstract decomposable class | `decomposableExactUpperAt_six` | [`E3FiniteReduction.lean`](ErdosSzekeres/E3FiniteReduction.lean) | class from Baek–Balko 2026 |

The three upper bounds formalize published results in explicit form; none of
them improves on the published bound. Full citations are in
[`docs/bibliography.md`](docs/bibliography.md).

### How `ES(6) = 17` is checked

`ES(6) = 17` was first established by exhaustive computer search
(Szekeres–Peters 2006). Marić (2019) reports a proof in Isabelle/HOL. In
Lean, the empty-hexagon verification of Subercaseaux et al. (ITP 2024) states
the six-point SAT result as an axiom (`unsat_6gon_cnf`), checked outside Lean.

Here the solver's proof is checked by the Lean kernel itself:

1. [`AnchoredPresentation.lean`](ErdosSzekeres/AnchoredPresentation.lean)
   proves that every configuration can be re-indexed so that one point sees
   every later pair as a right turn. This symmetry break makes the instance
   small enough to solve.
2. The anchored seventeen-point instance (680 triple variables, 217,176
   clauses) is refuted by CaDiCaL in about five minutes, with an LRAT proof.
3. The 59,684-clause unsatisfiable core and its LRAT proof are replayed in the
   kernel through 192 checkpoint modules: 5.4 hours of compile time in
   total, with a peak of 17.7 GiB.

`forces_six` therefore depends only on the standard axioms. Experiment 0109
records the inputs, hashes, solver runs and the `#print axioms` output. The
level-6 predecessor-half theorem uses the same method on a 15-point instance
(256 checkpoint modules, experiment 0110).

### The main route: predecessor halves

`PredecessorHalfSubsetAt k` says that every set of points with no `k` in convex
position contains at least half of its points with no `k-1` in convex
position (stated in the sweep-coloring model; see
[`StrongPredecessorBicoloring.lean`](ErdosSzekeres/StrongPredecessorBicoloring.lean)).
A doubling argument shows that this property at every level gives the full
conjecture, and that reduction compiles. Levels 4, 5 and 6 are proved; level 7
and above are open. The statement, the reduction and the evidence collected
for higher levels are in
[`docs/plans/predecessor-half-conjecture.md`](docs/plans/predecessor-half-conjecture.md).

## How the work is organized

- **Lean libraries.** `ESCore` (rooted at
  [`ErdosSzekeres.lean`](ErdosSzekeres.lean)) holds every proved result,
  including the generated certificate modules. `ESBlueprint` holds one module
  per open statement and is the only place `sorry` is allowed.
- **The `es` harness** ([`tools/es`](tools/es), design in
  [`docs/harness-design.md`](docs/harness-design.md)) derives project state
  from the compiled Lean environment, not from hand-kept notes. It runs the
  axiom audit against [`harness/allowlist.json`](harness/allowlist.json) and
  locks every statement by the hash of its type in
  [`harness/statements.lock`](harness/statements.lock), so a proof cannot
  quietly change what it proves (restatements are logged in
  [`harness/restatements.md`](harness/restatements.md)). It also runs
  long computations as memory-capped, recorded jobs. A general version of
  the harness is published separately as
  [lean-lockstep](https://github.com/GLitchfield/lean-lockstep).
- **AI agents.** The Lean development, scripts and experiment notes were
  written with AI coding agents (Claude Code and OpenAI Codex). The working
  rules every agent follows are in [`CLAUDE.md`](CLAUDE.md) and
  [`AGENTS.md`](AGENTS.md).
- **Research record.** Numbered experiment notes with predeclared pass/fail
  gates are in [`docs/experiments/`](docs/experiments/), indexed in
  [`docs/research_log.md`](docs/research_log.md). The strategy map and its
  tickets are in [`docs/wayfinder/`](docs/wayfinder/). The detailed
  progress log through 4 September 2026, which this README used to carry, is
  [`docs/progress-log.md`](docs/progress-log.md).

## Building and checking

**Requirements.** Lean is installed through
[elan](https://github.com/leanprover/elan); the toolchain is pinned in
`lean-toolchain` (Lean and mathlib `v4.29.1`). The harness needs Python 3.12.
A full build of `ESCore` produces about 130 GB of build files, and the
largest certificate modules are built under memory caps of 20–28 GiB each.
Hosted CI runners cannot do this, so CI runs only the harness tests and the
layering check.

```console
uv venv tools/es/.venv && uv pip install -e "tools/es[test,mcp,research]"
make update                      # lake update: fetch mathlib and LeanHammer
tools/es/bin/es doctor           # check toolchain, config, build files and database
tools/es/bin/es build core       # memory-guarded, budgeted build of ESCore
tools/es/bin/es audit            # non-standard axioms vs harness/allowlist.json
tools/es/bin/es status           # the frontier: open, claimed and closed statements
make harness-test                # layering, extract consistency, axiom audit, harness unit tests
```

Do not run a bare `lake build` on the full library: the harness keeps the
large certificate modules within the memory budget in
[`harness/config.toml`](harness/config.toml). The generated certificate
modules come from the `scripts/generate_*.py` producers, and each experiment
note lists the exact commands. For example, the `ES(5)` encoding and its Lean
bridge:

```console
python3 scripts/generate_es5_sat.py certificates/es5-signotope.cnf \
  --lean ErdosSzekeres/ES5CNFGenerated.lean
```

See [`docs/reproducibility.md`](docs/reproducibility.md) and
[`docs/automation.md`](docs/automation.md) for more.

## Layout

```text
ErdosSzekeres/        proved Lean development (ESCore), including generated certificate modules
ESBlueprint/          open statements, one module each (sorry allowed only here)
certificates/         CNF encodings and LRAT proofs replayed by the certificate modules
harness/              generated frontier, statement lock, axiom allowlist, research library
tools/es/             the es harness (CLI and MCP server)
scripts/              certificate generators, checkers and enumerations
data/derived/         computed results that experiments cite
docs/experiments/     numbered experiment notes
docs/wayfinder/       strategy map and tickets
docs/research/        archived agent research write-ups
runs/                 machine-local work (ignored by git)
```

## License

MIT; see [`LICENSE`](LICENSE). The cup–cap recurrence in
[`ErdosSzekeres/CupCap.lean`](ErdosSzekeres/CupCap.lean) adapts Jineon Baek's
Apache-2.0 formalization
[`jcpaik/erdos-tuza-valtr`](https://github.com/jcpaik/erdos-tuza-valtr), and
the Wayfinder planning framework is adapted from Matt Pocock's MIT-licensed
[`mattpocock/skills`](https://github.com/mattpocock/skills). See
[`NOTICE`](NOTICE) for details. The repository started from
`open-math-research-template`.
