# Rooted span-interface gate

## Reviewed contract

After the unrooted dominance quotient failed, a bounded Sol/Fable review at
git revision `b9a94e02c8cba656708afb05433ac227a4980ae0` selected one final
specification-level interface test. The evidence packet had SHA-256
`593e6f8cc88c4c7d7c26175f5d1a864472af90f80e179aa0c83ab783d5cc8aa6`.
The Fable and Sol result hashes were respectively
`b8b72934ab1648102e5191b6ab04ff47f4c98407690763b3e1191822a5040129`
and `86587728a787968b5e19386490a0df67c6a43b552aba05d7df7673c246ae23ed`.

Both reviewers required a rooted interface to be rejected on either a
transition collision or injectivity across all 46,699 raw child classes. The
reviewed stop condition redirects to structural counting if the natural
finite interface repairs are refuted or vacuous. Reviewer agreement is route
advice, not mathematical evidence.

## Candidate

For a cut `c`, the recursive rooted state contains:

1. the exact raw endpoint-span footprint on pairs wholly left of `c`;
2. the exact raw endpoint-span footprint on pairs wholly right of `c`; and
3. a multiset of crossing ports.

A crossing span with endpoints `a < c <= b` and exact cup/cap rank code `r`
has port

```text
(min(d, c-a), min(d, b-c+1), r).
```

Port multiplicities are clipped at `k`. A terminal strong-`k` child has one
distinguished terminal state. Thus the interface component is finite in `k`
and fixed depth `d`; the two exact side states recurse. This is not a claim
that the complete state is a flat finite `k`-only quotient.

The transition gate distinguishes either root of a two-vertex root block. If
the designated root occupies parent position `q`, its child cut is its gap
before insertion and the output is the rooted parent state at the cut directly
before or after `q`. Comparing parent rooted states, instead of demanding the
entire parent raw footprint, tests recursive congruence without making the
proposed compression vacuous by definition.

## Nonvacuity census

Two independent encoders enumerate the 46,699 distinct raw footprints of all
186,888 decomposable eight-vertex colorings at `k = 6`. At the middle cut the
class counts are:

| depth | rooted classes | merged fibers | largest fiber |
| ---: | ---: | ---: | ---: |
| 1 | 32,481 | 9,576 | 12 |
| 2 | 40,479 | 5,340 | 6 |
| 3 | 44,965 | 1,710 | 3 |
| 4 | 46,699 | 0 | 1 |

Depth three remains noninjective at every one of the seven internal cuts.
Depth four is already injective at the middle cut. Depth three is therefore
the strongest nonvacuous cut-relative depth at this first decisive boundary.

## Transition refutation

Depth three fails in the lower-root context with roots at parent positions
`[0,5]`, the second root distinguished, and the output cut immediately before
that root. Six depth-three signature fibers collide. The first contains child
colorings

```text
17cf47ffe5a350
17cf4fffe5a340
```

At child cut four their raw footprints differ only at:

```text
(0,6): 24 / 34
(1,7): 34 / 24
```

Each span has one endpoint at cut-distance four and the other at distance
three, so both capped distance pairs are `(3,3)` and the port multisets agree.
After adjoining the roots, the open parent footprints differ at:

```text
(0,8): 33 / 43
(1,8): 24 / 34
(2,9): 34 / 24
```

Their rooted parent signatures at cut five are unequal. The producer locates
the collision in the digest-checked raw machine table. The independent
checker reads no machine table: it regenerates all raw child classes and the
two parents directly from coloring bits, reproducing the complete census,
child equality, parent inequality, and exact differing pairs.

Increasing the depth to four separates the witness only by making the child
state injective at this cut. This fires both reviewed rejection branches:
depth three is not a transition congruence, and its immediate finite-depth
repair is vacuous on the complete observed raw class set.

## Formal obstruction to a dominance-only repair

Retaining the ordered incidence of all nondominated ports is not automatically
a `k`-only repair. `SpanDominance.lean` now defines simultaneous left/right
extension dominance. The compiling theorem
`twoSidedExtensionDominates_diagonal_iff` proves, for every ambient size `m`,
that equal-rank diagonal ports dominate one another exactly when their indices
are equal. Hence the two-sided dominance order has arbitrarily large
antichains. The existing one-sided dominance theorems alone cannot bound an
ordered port frontier independently of ambient size.

## Disposition

The rooted finite-interface route is stopped. This bounded result does not
refute the raw span footprint, the decomposable exact formula, or the general
Erdős--Szekeres conjecture. It refutes one finite-depth recursive quotient and
proves that the obvious exact ordered-frontier repair lacks the promised
`k`-only bound.

The pre-vetted redirect is structural counting. Its first named contract is
`allocatedSpanPascalDemand_le_window`: exact near-threshold span witnesses are
allocated to the unique lowest decomposition-tree node separating their
endpoints; the adjacent Pascal coefficients supported by those spans must be
charged injectively into the outer `decomposableBinomialWindow`. The contract
must define the demand from the existing `publishedChildIndex` and exact span
ranks, state the allocation map, and prove the window inequality before it may
be used in E3. The raw footprint is local evidence for that charge, not the
global induction state. A bounded falsification at the committed `k = 6`
boundary precedes Lean promotion of this counting statement.

## Reproduction

```console
python3 scripts/enumerate_rooted_span_interfaces.py \
  --raw-run-directory runs/e3-two-root-span-k6-n10 \
  --output data/derived/e3-rooted-span-interface-k6-n10.json
python3 scripts/check_rooted_span_interfaces.py \
  data/derived/e3-rooted-span-interface-k6-n10.json
```
