# E3 all-root context-profile replay

## Status and scope

This is bounded computational evidence, not a completed mathematical result.
It covers every distinct recursively deep-below triple coloring on `1 <= n <=
8` ordered leaves and every compatible root split of each coloring.  It does
not establish straight-line realizability and does not prove any all-`k`
bound.

The experiment answers the finite gate selected after the post-six route
review: replace the previous one-tree-per-coloring census by an all-root
replay, attach directional anchor contexts, test restriction and composition,
and redirect if a proposed summary loses information.

## Profile under test

An external anchor is placed at a sweep gap `g`, before vertex `g`, where
`0 <= g <= n`.  Every nonempty chain lies in exactly one directional class:

- `L`: the anchor lies left of the whole chain;
- `R`: the anchor lies right of the whole chain;
- `S`: the chain has a vertex on each side and strictly straddles the anchor.

For `k = 5`, the anchored profile is the seven-tuple

```text
(max cup L, max cup R, max cup S,
 max cap L, max cap R, max cap S,
 contains a strong 5-set),
```

where each maximum is clipped at five.  Thus the alphabet is finite for this
fixed `k`.  The census encountered 949 profile values through eight leaves.

Three proposed composition inputs were tested at every compatible root and
every external gap:

1. **same-gap:** the two child profiles at the external gap;
2. **cross-anchor:** same-gap data plus the sibling profile seen from every
   vertex in the opposite child;
3. **all-gap:** the complete ordered profile word of each child at every gap.

The root membership word is fixed structural input in each transition table;
it is not silently discarded.  An **open** transition is one whose parent has
no strong five-set.  Closed transitions already satisfy the target
alternative and are reported separately.

## Producer and checker

`scripts/enumerate_decomposable_contexts.py` constructs colorings and roots
bottom-up from pairs of child colorings.  It streams canonical hashes rather
than writing millions of records.  For every root it hashes the complete
color vector, lower set, cup-5/cap-5/strong-5 flags, and signotope flag.  For
every opposite-child anchor it separately hashes every sibling four-cup and
four-cap, including the chain vertex mask and `L`/`R`/`S` relation.

`scripts/check_decomposable_contexts.py` imports no producer code.  It builds
its own coloring recurrence, then reverses the root-enumeration direction: for
each parent color vector and candidate lower set it restricts the parent,
checks recursive membership of both restrictions, and checks every mixed
triple against the root law.  It independently recomputes chains, profiles,
restriction comparisons, collision witnesses, record hashes, and all summary
counts.

The final producer took 1 minute 19 seconds and 301 MiB peak RSS.  The
optimized independent replay took 1 minute 58 seconds and 302 MiB peak RSS.
Both are inside the declared 30-minute, 16-GiB experiment bound.

## Exact coverage and results

Across all eight layers the census contains:

- 198,276 distinct colorings (186,888 at eight leaves);
- 243,102 compatible roots (228,112 at eight leaves);
- 180,436 singleton-child roots;
- 1,896,168 anchor/four-chain records, of which 1,523,760 occur at
  singleton-child roots;
- 948,084 exact endpoint-extension checks;
- 205,926 forbidden-extension/forced-straddling checks;
- 4,343,048 child-to-parent restriction checks.

There are zero endpoint, saturation, or restriction violations.  In
particular, the census independently reproduces the compiled local Lean
lemmas at every covered root, rather than only at one retained witness tree.

The profile-composition outcomes are discriminating:

- same-gap has 5,445 collision observations on open branches, first at five
  leaves;
- cross-anchor has 1,192 collision observations on open branches, first at
  six leaves;
- all-gap has zero collisions among 47,400 open observations and 8,800
  distinct open inputs through eight leaves;
- without the no-strong-5 guard, all-gap has 3,839 collision observations;
  its first collision is at seven leaves and is already a closed branch.

At eight leaves alone there are 28,422 open observations, 3,654 distinct
all-gap open inputs, and zero all-gap open collisions.  The smaller
cross-anchor state has 752 open collision observations at that layer.  A
canonical first eight-leaf cross-anchor collision is recorded in the manifest
at lower mask `0x2`, external gap `5`: two parents with the same input profile
produce parent profiles that differ in the cap maximum on the anchor-right
side (`4` versus `3`).

The independent checker agrees on the complete layer data, the 949-element
alphabet, and all three canonical hashes:

```text
coloring records:
  da8f1bca27763387ba6442dd70aefc89e76daaf1a492bfcb7b9af8489d62befc
root records:
  c055ad94273c3965f36ea5ee53b936d0d449d635980c9eefc9c2fd19cd2e1b27
anchor/four-chain records:
  b28f344c71541d480737ee6609859d6a72e598d8c744057bd26721fca32865b7
profile alphabet:
  5949cb7835532092670cf21315d02c33494e8d650201d3316824c140b66c54d0
```

The machine-local canonical manifest is `runs/e3-contexts-n8.json`.

## Interpretation and redirect

The same-gap profile is refuted as a compositionally complete state.  Adding
only contexts supplied by current sibling vertices is also refuted.  These
are finite witnesses to the reviewer concern that local endpoint information
can lose ancestor context.

The all-gap word survives the bounded open-branch test, but its length grows
with the number of vertices.  Therefore this experiment does **not** justify
an injection into `2^(k-2)` states, does not repair the published scalar
recurrence, and does not yet select candidate B as the uniform main route.
It supplies a precise transition conjecture and a safe first definition
layer, while preserving the redirect: a proof that requires carrying the
whole word without a bounded compression sends the project back to a richer
rank/downset invariant or a different counting argument.

## Proposed Lean transition candidate

First define, for general `k`, a `SweepGap n := Fin (n + 1)` and an
`AnchoredMaxProfile k chi s g` containing the six clipped directional
cup/cap maxima and the `ContainsStrongPolygonSet chi s k` flag.  The first
unconditional Lean obligation is the restriction law

```text
t subset s ->
AnchoredMaxProfile k chi t g <= AnchoredMaxProfile k chi s g
```

componentwise.  This removes the reviewer's previously undefined hereditary
transport without assuming any composition theorem.

The bounded evidence then supports challenging the following theorem shape,
not claiming it:

```text
given two colorings chi and psi with the same lower/upper root sets,
recursively decomposable children, and HasDeepBelowSplit at that root,
if their lower profiles agree at every sweep gap,
and their upper profiles agree at every sweep gap,
and neither parent contains a strong k-set,
then their parent profiles agree at every sweep gap.
```

The first attempted instance should be `k = 5`.  A useful general theorem
must then either prove a bounded compression of the all-gap word or avoid
storing it.  Merely proving the fixed-`k=5` finite instance would validate the
definition and transition semantics but would not advance the all-`k` count.

## Reproduction

```console
python3 scripts/enumerate_decomposable_contexts.py \
  --maximum-n 8 --output runs/e3-contexts-n8.json
python3 scripts/check_decomposable_contexts.py runs/e3-contexts-n8.json
```

Rational-coordinate realizability is explicitly `not_attempted` in the
manifest because these abstract recursive-coloring certificates carry no
coordinates.  No geometric conclusion is inferred from the census.
