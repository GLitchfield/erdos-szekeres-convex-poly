# Experiment 0096: strong-predecessor property B

Date: 2026-08-10

Status: Exact recurrence hierarchy and small-cardinality base compile; bounded
`k = 5` certificate checks; general producer remains open

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

## Weaker recurrence contract and uniform base region

Lean now separates the structural content needed by the recurrence from the
full two-coloring. `PredecessorHalfSubsetAt k` asks only for one
strong-`(k-1)`-free subset containing at least half the vertices. The following
implications compile:

```text
integral bicoloring -> fractional cover -> half subset -> exact recurrence.
```

The direct integral-to-half and fractional exact-doubling proofs also compile,
providing independent checks of the hierarchy. None of these implications
constructs its source contract.

A new certificate-free base theorem proves something uniform rather than
merely finite: for every `k >= 5`, every strong-`k`-free coloring on at most
`2*k-3` vertices has a predecessor bicoloring. The proof uses only the
four-index strong-polygon law and is stronger than a realizable statement.
At the top cardinality, if every `(k-1)`-set were strong, then every ordered
quadruple of a `k`-set would survive in a strong predecessor subset, making the
whole `k`-set strong. This contradicts the hypothesis and supplies one free
class; its complement is too small to contain a predecessor polygon.

At `k=6` this theorem formally covers `n<=9`. Independent semantic CNF
generation and LRAT replay found no integral/fractional/half separator for
abstract rank-three signotopes through `n=11`; corrupted controls and a repeat
run were rejected/confirmed as expected. The `n=10` and `n=11` extensions are
computational evidence, not Lean theorems. The canonical result SHA-256 is
`d6acc56f197cb4620c2f22a80a5beccfd75a6674cbb59ba4b8342eed42086708`.

## Retired maximum-support exchange

A proposed construction from a maximum predecessor-free support is now
stopped. Replacing one point of a disjoint predecessor polygon while deleting
at most two support vertices would produce a predecessor-free set strictly
larger than the declared maximum. The premise is nonvacuous: an independently
checked eight-point integer-coordinate configuration has no strong five-set,
has 46 maximum strong-four-free supports and 14 eligible support/polygon
pairs, and all 616 exchange trials fail. This refutes that exchange contract,
not predecessor bicoloring, fractional cover, or the half-subset route. The
canonical computational result SHA-256 is
`7549842cd46ea2886debedc0fc14a7febc7bbdbbc3cda3b238f4248a12ea7339`.

## Route disposition

`GO_ON_PREDECESSOR_HIERARCHY__STOP_MAXIMUM_SUPPORT_TWO_DELETION_EXCHANGE`.

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
