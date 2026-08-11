# Experiment 0096: strong-predecessor property B

Date: 2026-08-10

Status: Exact recurrence interface compiles; bounded `k = 5` certificate checks;
final Lean semantic bridge pending

## Question

Can every realizable coloring with no strong `k`-polygon be partitioned into
two vertex classes that both avoid a strong `(k-1)`-polygon? Such a partition
would give the exact doubling recurrence without first constructing a
decomposition tree.

## Compiling recurrence

`StrongPredecessorBicoloring.lean` defines the exact hypothesis
`StrongPredecessorBicoloringAt k`. Lean proves the base case

```lean
sweepExactUpperAt_three : SweepExactUpperAt 3
```

and the load-bearing consumer

```lean
sweepExactUpperAt_of_predecessorBicoloring
    (hprev : SweepExactUpperAt (k - 1))
    (hbicolor : StrongPredecessorBicoloringAt k) :
    SweepExactUpperAt k
```

for `4 ≤ k`. The proof restricts the swept coloring to each class, transports
any predecessor polygon back to the ambient support, and bounds both classes
by `2^(k-3)`. Their disjoint union therefore has at most
`2 · 2^(k-3) = 2^(k-2)` vertices.

This implication is a completed Lean theorem. It does not prove the
bicoloring hypothesis.

## Bounded first gate

A deterministic CNF producer and an independent non-CNF, eight-valued
quadruple CSP checker both found the following search UNSAT:

- ground sizes `n = 7` and `n = 8`;
- the rank-three signotope law;
- no strong five-set;
- no red/blue partition whose two classes both avoid a strong four-set.

The stronger balanced gate also passes: every strong-five-free rank-three
signotope on eight vertices in the bounded audit has a `4+4` partition with
neither block strong four.

The bounded claim now has a deterministic exhaustive DPLL-tree certificate for
the exact 126-variable, 1,211-clause `Fin 8` formula.  The tree is 24,882 bytes,
and an independently written semantic checker reconstructs the quadruple CSP,
replays the certificate, and rejects a corrupted certificate.  A generated
1.53-MiB LRAT proof also checks at the bare propositional layer in Lean.

This is checkable computational evidence, not yet a completed mathematical
result under the project standard.  The final semantic theorem must still
connect every retained propositional clause to `OneChangeOn`, strong-five
avoidance, and the repository's balanced bicoloring predicate.  Since the
abstract signotope search found no witness, no rational-realization step was
needed. The result supports the realizable contract because the abstract model
is a superset, but it does not prove the unbounded statement.

## Route disposition

`GO_AT_K5_BOUNDED_GATE`.

This route is structurally independent of state 578 and of Layer-F mutation
normalization. It explains the exact exponent directly through a binary
recurrence, rather than merely transporting an already proved decomposable
bound.

The exact formal target remains the generated certificate theorem

```lean
strongFiveFreeSignotopeFinEight_balancedBicoloring
```

The encoding, bare LRAT theorem, and a complete semantic chunk compile.  Two
single-job attempts at the global semantic specialization approached or
exceeded the 16-GiB project ceiling and were terminated safely; no failed or
yielded build is counted as a theorem.  Opaque atom names and branch-local
elimination reduced intermediate memory but did not close the final target.
Deterministic exact core minimization removed only 16 clauses, taking the
formula from 1,211 to 1,195 clauses.  The independent checker reconstructed
the retained semantic map, replayed the fresh certificate, and rejected
corrupted certificate and map controls.  The certificate itself grew by
27.3%, however, so this 1.3% semantic reduction is not expected to resolve the
Lean memory bottleneck.  Core minimization is therefore stopped as the active
repair.  The bounded theorem remains open pending a substantially different
semantic-bridge architecture or an explicitly approved higher-memory check;
no higher-memory result is claimed.

After exact promotion, the mathematical question is whether the balanced
partition has a structural construction that extends to arbitrary `k`, or
whether the next bounded instance supplies a counterexample.

Experiment 0101 formalizes a strictly weaker incidence-level relaxation:
fractional predecessor covers of total weight two. Its exact-doubling consumer
compiles, but the first abstract-signotope gate does not distinguish the
fractional condition from the integral bicoloring tested here.

## Evidence and resources

- `ErdosSzekeres/StrongPredecessorBicoloring.lean`
- `runs/agents/20260810-property-b-audit/audit-report.json`
  (SHA-256
  `e7fa7c95dc95c07f8d40ef788ebf84f9ff1f4043ec53af7f36ca5f86a6329992`)
- longest bounded search: 5.48 seconds
- peak RSS: 20,368 KiB
- output: 76 KiB
- targeted Lean build: 3,326 jobs
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- balanced CNF SHA-256:
  `75cab86f23e12fb30832c4db875a03b9dcda53f560353423233d31a8a311db0a`
- DPLL tree SHA-256:
  `84836242d68a3d9e3a16a1e3ad8c347ead43a33cb6054f42f1a6d386da5cd37c`
- generated LRAT SHA-256:
  `00c4fc9965cc5979627970b814c125197763b41aed4943a4b6c8aee1968a55c2`
- minimized 1,195-clause CNF SHA-256:
  `5399775d144751e3ec2014a642f994a459926d28a061fe165ef3f1c1316f4f84`
- canonical minimization result SHA-256:
  `681b8deb88d8ccabb34f697b2911f262270dded43deadf5db1d9f8647ecd30cd`
