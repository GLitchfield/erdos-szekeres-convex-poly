# ES(5) finite certificate

`es5-signotope.cnf` has one Boolean variable for each of the 84 increasing
triples on nine ordered vertices. Its 2,016 clauses consist of:

- 1,008 clauses excluding the eight non-one-change patterns on each of the
  126 four-subsets; and
- 1,008 clauses excluding the eight strong-polygon patterns on each of the
  126 five-subsets.

Regenerate the CNF and the semantic Lean modules with:

```console
python3 scripts/generate_es5_sat.py certificates/es5-signotope.cnf \
  --lean ErdosSzekeres/ES5CNFGenerated.lean
```

The committed LRAT trace was produced with CaDiCaL 1.7.3:

```console
cadical --lrat --no-binary \
  certificates/es5-signotope.cnf certificates/es5-signotope.lrat
```

Checksums:

```text
322c753bd3189b97fd381d7363c8b4aaa7e7c4a59d9d993b0da6ce75fe1ca09e  es5-signotope.cnf
741e74e9c5df5adfad2b0b99534ad5fe184ddc1658de6d0545135f2a470c2a50  es5-signotope.lrat
```

The solver is not trusted. `ErdosSzekeres/ES5Unsat.lean` checks the LRAT trace
inside Lean, while the generated chunk modules prove that every encoded clause
follows from `TurnSequenceAllowed` or the assumption that a five-subset is not
strong.

## E3 finite-state certificates

The E3 reduction at six vertices uses two one-change-coloring instances.  A
state `(n,a,u,k)` excludes an `a`-cap, a `u`-cup, and a strong `k`-set on `n`
ordered vertices.

| state | variables | clauses | CNF SHA-256 |
| --- | ---: | ---: | --- |
| `(12,4,6,6)` | 220 | 20,163 | `c8b69888f91a0da669d43c249cd0962cc0db33fe3072a1e1bed4d9df1b4a8830` |
| `(16,5,6,6)` | 560 | 155,064 | `d79d91b2f10ddb6321be3987067a135b9264256debaafa97cd97e38ffe8bb857` |

The twelve-vertex LRAT file is committed directly and has SHA-256
`765420d2a2adf0174d5199e5328608afb126484fd40f435a4db93909d9231e74`.
The trimmed sixteen-vertex LRAT proof has 1,667,699 learned additions, ends at
clause 1,822,763, contains 496,453,316 bytes, and has SHA-256
`3143c8bcdb72c22c1d269317512bd9b98b02b9f14f414510b5485a4896ce9dc6`.
It is committed as 256 ordered segment files under
`e3-state566-checkpoints/`; concatenating those files reproduces that byte
count and hash.

`LRATCheckpoint.lean` checks each segment with Lean proof constructors and
exports only the live clauses needed by the next segment.  The last segment
proves the empty clause.  The generated CNF modules separately prove that all
155,064 input clauses follow from the one-change law and the three forbidden
configuration assumptions.  Consequently the external SAT solver, LRAT
trimmer, splitter, and generators are not trusted proof oracles.

The sixteen-vertex semantic bridge is deliberately layered to keep Lean's
elaboration bounded: 769 semantic clause chunks feed 4,096 raw aggregation
modules, which feed 1,024 midpoint modules.  Short named propositions then
form the final disjunction tree.  A separate Lean module proves by `rfl` that
this named tree is definitionally equal to the canonical 155,064-clause
checkpoint proposition, so the final transport does not rely on a textual or
external-oracle assertion.  On the completion build, the named aliases took
7.2 seconds with 2.36 GiB peak RSS, the named root took 9.5 seconds with 2.17
GiB, and the single full-size definitional bridge took 49 seconds with 2.62
GiB.  The older twelve-vertex aggregation completed in 195 seconds with 3.64
GiB peak RSS; the complete cached-recovery build of `E3FiniteReduction`
finished all 9,611 jobs successfully.

`scripts/check_e3_state566_aggregation.py` is an independent whole-data
checker: it imports neither generator, reparses the canonical DIMACS file,
checks its metadata digest, reconstructs every proposition tree, and verifies
all generated imports, aliases, hypotheses, elimination leaves, and the bridge
source.  Its completion result was `clauses=155064`, `raw=4096`,
`midpoints=1024`, with CNF SHA-256
`d79d91b2f10ddb6321be3987067a135b9264256debaafa97cd97e38ffe8bb857`.

Reproduce the canonical sixteen-vertex inputs and generated Lean sources with:

```console
python3 scripts/generate_signotope_state_sat.py \
  --n 16 --cap 5 --cup 6 --strong 6 \
  --output certificates/e3-signotope-16-5-6-6.cnf
python3 scripts/split_lrat_checkpoints.py \
  certificates/e3-signotope-16-5-6-6.cnf \
  runs/e3-signotope-16-5-6-6-trimmed.lrat \
  certificates/e3-state566-checkpoints \
  --original-clauses 155064 --segments 256 \
  --lean-prefix E3State566Checkpoint --lean-dir ErdosSzekeres \
  --bundle-size 100000 --bundle-size-override 99:4096 --quiet
python3 scripts/generate_e3_state566_lean.py ErdosSzekeres \
  --core-cnf certificates/e3-signotope-16-5-6-6.cnf --chunks 256
python3 scripts/check_e3_state566_aggregation.py
```

The bundle override changes only the organization of the segment-99 Lean
proof term; it keeps compilation within the documented memory bound and does
not change the LRAT data or theorem.  The machine-local monolithic trimmed
trace remains under ignored `runs/`; the committed segments are the complete
proof data consumed by Lean.
