# E3 adversarial experiment design

## Exact object being tested

A recursive deep-below coloring has a full binary decomposition tree whose
leaves are sweep indices.  At an internal node, a triple meeting both children
is left exactly when its middle sweep index belongs to the lower child; a
triple contained in one child is evaluated recursively.  This is the finite
tree semantics of `HasDeepBelowSplit` used by the current prototype.

For a fixed `k`, the falsification target is a coloring on more than
`2^(k-2)` leaves that has no `k`-element subset satisfying both strong-polygon
four-index equalities.  The target relevant to the Lean theorem must also be
sweep-realizable.  The rank-three signotope law is a necessary but not
sufficient certificate of straight-line realizability and is therefore
reported separately.

## Known proof obstruction

The journal induction chooses auxiliary values `u'` and `a'`.  At
`(a,u,k,u',a') = (4,5,5,1,3)`, its asserted cardinal contributions evaluate
to

```text
S(4,1,5) + choose(3,0) + S(3,5,5) + choose(3,2) = 8,
S(4,5,5) = 7.
```

The first added binomial term is retained even though the Pascal interval into
which the proof later places it is empty.  This invalidates that induction
step but does not constitute a counterexample to E3.

## Producer plan

1. Enumerate decomposition trees with labeled sweep leaves, canonicalizing by
   the induced triple-color bit vector so duplicate decompositions are merged.
2. For each coloring, compute cup, cap, and strong subset maxima exactly.
3. Shard deterministically by a prefix of the color bit vector or canonical
   split code; write atomic shard summaries and any first counterexample.
4. If exhaustive enumeration stops being feasible, formulate the same finite
   conditions as SAT and retain a replayable assignment or unsatisfiability
   certificate rather than relying on solver status.

## Independent checker

The checker will read only a compact leaf count, tree certificate, and claimed
triple-color vector.  It will reconstruct colors from the tree, compare every
triple bit, enumerate all `k`-subsets, check both strong equalities on every
four-subset, and independently check the signotope law.  A geometric branch
additionally needs rational coordinates and exact determinant signs.

## Outcome branches

- **Certified realizable counterexample:** refute the current E3 statement and
  redirect Layer E immediately.
- **Abstract-only counterexample:** repair `IsDecomposable` or strengthen its
  realizability data before further proof work.
- **No counterexample within exhaustive bound plus stable invariant:** select
  the invariant only after Sol/Fable review and prove its first transition in
  Lean.
- **No counterexample without structural signal:** record a bounded negative
  computation and redesign; do not continue an unbounded search.

## Evidence classification

Until an independent checker and coverage manifest exist, results from
`scripts/decomposable_profile_search.py` are heuristics.  A completed bounded
enumeration is an exact computation only within its declared finite bound.  E3
is complete only with a kernel-checked Lean proof.

## Exact enumeration results

The dynamic-programming producer and a separately implemented checker agree
through eight labeled leaves.  For `n <= 7` the checker explicitly enumerates
every ordered labeled full binary tree; at `n = 8` it uses an independent
subset recurrence after the explicit implementations were cross-checked at all
smaller sizes.

| leaves | ordered trees | distinct colorings | minimum strong maximum |
|---:|---:|---:|---:|
| 4 | 120 | 8 | 3 |
| 5 | 1,680 | 62 | 4 |
| 6 | 30,240 | 718 | 4 |
| 7 | 665,280 | 10,596 | 4 |
| 8 | 17,297,280 | 186,888 | 4 |

All 198,272 distinct colorings across the five completed top layers satisfy
the rank-three one-change law.  This supports, but does not prove, the proposed
structural lemma that recursive deep-below colorings are signotopes.

At eight leaves, exactly 2,862 colorings have no strong five-set.  Every one
has cap maximum four and cup maximum four.  Thus the finite statement suggested
by the blind Fable review--every eight-leaf decomposable coloring contains a
four-cap or a strong five-set--survives exhaustive enumeration, as does its
cup-dual.  This is exact finite evidence for a potential base lemma, not yet a
Lean theorem and not evidence for the all-`k` induction.

The committed tools are `scripts/enumerate_decomposable_colorings.py` and
`scripts/check_decomposable_enumeration.py`.  Run manifests under `runs/` record
the complete coloring hash, profile histograms, a minimizing tree witness, and
all independent-check results; `runs/` is intentionally machine-local.

## First `k = 6` falsification states

The reciprocal Fable review proposed auditing two off-diagonal states before
attempting a 17-vertex diagonal proof.  The new CNF generator imposes the
one-change law and forbids the specified cap, cup, and strong-set sizes.  Since
Lean proves that every decomposable coloring is a signotope, UNSAT at this
larger signotope level rules out a decomposable witness once the semantic CNF
bridge is checked.

| state | variables | clauses | solver result | certificate status |
|---|---:|---:|---|---|
| `(n,a,u,k) = (12,4,6,6)` | 220 | 20,163 | UNSAT | 1.4 MiB LRAT trace accepted by Lean's kernel as a CNF theorem |
| `(n,a,u,k) = (16,5,6,6)` | 560 | 155,064 | UNSAT | 496,453,316-byte trimmed LRAT split into 256 Lean-kernel-checked checkpoints |

The first CNF has SHA-256
`c8b69888f91a0da669d43c249cd0962cc0db33fe3072a1e1bed4d9df1b4a8830`.
The second has SHA-256
`d79d91b2f10ddb6321be3987067a135b9264256debaafa97cd97e38ffe8bb857`.
The generator has independent unit tests for clause accounting and the count
of strong assignments.

The twelve-vertex result is now a semantic Lean theorem.  Its checkpoint chain
kernel-checks the LRAT trace, the generated balanced bridge connects all 20,163
clauses to the project predicates, and
`E3State466Certificate.lean` proves that every twelve-vertex one-change
coloring has a four-cap, a six-cup, or a strong six-set.  The theorem therefore
applies to every recursively decomposable coloring.

A proof-size audit of the sixteen-vertex state led to a practical checkpoint
representation.  The final trimmed trace has 1,667,699 learned additions and
496,453,316 bytes.  `LRATCheckpoint.lean` checks it as 256 sequential proof
modules, exporting only live clauses between segments; generated CNF chunks
derive all 155,064 input clauses from the project predicates.  The semantic
theorem `exists_cap_five_or_cup_six_or_strong_six` promotes by restriction to
`decomposableStateUpper_566`, and the finite reduction proves
`decomposableExactUpperAt_six`.  Solver exit codes and reviewer reasoning are
not used as proof.

The first expanded 4,096-way root and a later 1,024-way root did not elaborate
within their bounded trials.  A reciprocal Sol/Fable review recommended
separating short named propositions from one unavoidable full-size
definitional equality and adding an independent actual-data checker.  That
redesign now compiles: 769 semantic chunks feed 4,096 raw modules and 1,024
midpoint modules; named midpoint aliases feed a compact root; and Lean checks
one `rfl` bridge to the checkpoint proposition.  The independent checker
reparses the canonical DIMACS file and verifies every generated range,
proposition, import, alias, elimination leaf, and root association without
importing either generator.  It reports all 155,064 clauses exactly once and
the canonical CNF digest above.

The advisory review packet had SHA-256
`1c50d5ec1789727a630e1f34579968d11389cc2af3d26cb9e8ee3dd300f9247a`.
Both final reviewers classified the pre-redesign evidence as partially
supported with medium confidence; their material requests were discharged by
the independent checker, the named-proposition build, the successful root
compile, and the final Lean axiom audit.  The review remains advisory rather
than mathematical evidence.
