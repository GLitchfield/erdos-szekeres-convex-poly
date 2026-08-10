# Experiment 0080: predecessor-fiber shelling falsifier

Date: 2026-08-10

Status: symmetric endpoint-orientation rule refuted in Lean

## Question

Can every target-free recursively decomposable coloring assign Boolean labels
to vertices so that each exclusive left/right predecessor-rank fiber orients
both endpoints, with the labels then injective into `2^(k-2)` states?

## Frozen specification

For clip `d = k - 2`, coordinate `r` records whether a predecessor pair has
consecutive rank at least `r + 1`.  An exclusive left event forces the lower
endpoint bit to zero and the upper endpoint bit to one; an exclusive right
event forces the opposite values.  Ties impose no constraint.  Coherence is
defined independently of injectivity, a cardinal bound, or a target outcome.

## Bounded falsifier

The first failure is already `k = 5`, `n = 4`, on the all-right coloring.  At
coordinate one, pair `(1,2)` forces vertex two's bit to zero while pair
`(2,3)` forces the same bit to one.  Hence no coherent label exists, which is
stronger than a Hall or injectivity failure.

The producer reconstructs recursively decomposable colorings and computes
pair ranks by dynamic programming.  The independent checker imports neither
the producer nor the enumerator; it rebuilds the coloring by tree descent and
enumerates all chain prefixes.  The deterministic certificate has SHA-256
`22423274c34a25400d0dfd00c682a1b9364e067f55b0a452b626e9c1d075d96a`.

## Lean promotion

`PredecessorFiberShellingCounterexample.lean` defines the frozen coherence
predicate and proves:

- the explicit four-vertex coloring is recursively decomposable;
- no five-vertex strong polygon lies in its four-vertex support; and
- no shell-coherent `Fin 3` Boolean labeling exists.

The final contradiction uses the kernel-reducible finite pair-rank program,
not the external certificate.

## Outcome

The symmetric rule assigning both endpoint bits is expired.  This does not
refute all endpoint-indexed shellings, E3, state `(5,7,8)`, or the exact
Erdős--Szekeres formula.  Any repair must weaken or contextualize endpoint
orientation before asking for injectivity.

## Evidence

- `ErdosSzekeres/PredecessorFiberShellingCounterexample.lean`
- `scripts/produce_predecessor_fiber_shelling.py`
- `scripts/check_predecessor_fiber_shelling.py`
- `data/derived/e3-predecessor-fiber-shelling-k8.json`
