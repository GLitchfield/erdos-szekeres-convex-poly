# Published off-window auxiliary classification

## Question

After removing the now-formalized index-one singleton branches, what is the
smallest feasible scalar failure in the published decomposable-set induction,
and do the remaining failures have a common arithmetic shape?

This is a bounded arithmetic classification. It is not a proof for all
parameters and does not establish a geometric transition.

## Conventions and bound

The producer enumerates `5 ≤ k ≤ 20`, active parents

```text
4 ≤ a,u ≤ k,  k + 4 ≤ a + u,
```

and auxiliary parameters

```text
1 ≤ a' < a,  1 ≤ u' < u,  a' + u' ≤ k - 1.
```

A parameter state is feasible only if positive child cardinalities sum to
`decomposableThreshold a u k + 1` and lie in the exact adjacent-threshold
intervals that make `a'` and `u'` the maximal published child indices. A
scalar failure is a state in which the two contributions used by the
published calculation exceed the outer threshold.

The deterministic producer is `scripts/enumerate_published_offwindow.py`. The
independent checker `scripts/check_published_offwindow.py` does not import the
producer, reconstructs binomial coefficients using a Pascal table rather than
`math.comb`, and independently derives the feasible child interval. It also
evaluates the actual greatest-index definition at both endpoints of every
feasible cardinality interval. Since that greatest index is monotone in the
cardinality argument, endpoint agreement covers the whole interval without
assuming threshold monotonicity in its index. Its optimized replay takes
approximately 0.13 seconds and less than 16 MiB RSS.

## Result

Through `k = 20`, the certificate records:

- 14,220 scalar-failure parameter states;
- 7,752 failures compatible with actual complementary child sizes;
- 3,670,056 compatible child-cardinality splits;
- 6,120 feasible parameter states after removing `a' = 1` or `u' = 1`;
- zero violations of the saturated-off-window classification.

Every remaining feasible state has one of the two dual forms

```text
a' = a - 1  and  u' < k - a + 1,
u' = u - 1  and  a' < k - u + 1.
```

The smallest non-index-one state is

```text
(a,u,k,a',u') = (4,6,6,3,2).
```

Its outer threshold is 11, the failed scalar contribution is 16, and the only
child-cardinality pairs are `(2,10)` and `(3,9)`. The color-dual state is
`(6,4,6,2,3)`.

This identifies the next structural question precisely: an open
`(4,6,6)` parent at this branch has a lower child of two or three vertices and
an upper child of ten or nine vertices. Any proposed theorem must exploit
their shared deep-below context; applying independent child bounds merely
reproduces the five-unit scalar defect.

## Lean promotion

The observed saturation pattern is now an all-parameter theorem, not merely a
finite pattern. `published_left_child_le_outer_prefix` and its color-dual
suffix theorem allocate the two adjacent child thresholds to opposite parts
of the outer Pascal row. When neither auxiliary parameter is saturated, those
parts are disjoint. `published_nonsaturated_next_threshold_pair_le` therefore
bounds their sum by the outer threshold, while actual complementary child
cardinalities force the strict reverse inequality.

Consequently `published_feasible_auxiliary_saturation` proves for every active
admissible parent that a feasible auxiliary pair has exactly one of the forms

```text
a' + 1 = a  and  u' < k - a + 1,
u' + 1 = u  and  a' < k - u + 1.
```

The proof compiles with only `propext`, `Classical.choice`, and `Quot.sound`.
The bounded census remains useful as an independent regression and as evidence
that `(4,6,6,3,2)` is the first unresolved non-index-one boundary; its bounded
ordering claim has not been promoted to a separate all-parameter minimality
theorem.

## Provenance

- Certificate:
  `data/derived/e3-published-offwindow-k20.json`
  (`dc3d5bb6f4bcdaf63dafa8aaecb5fd16fa898d21d334a9e9c61ad866cd576403`)
- Producer:
  `scripts/enumerate_published_offwindow.py`
  (`c80baf9973ca8af6bf8ca112c8b88a65a7a2b070c893f1fd0b0d66e9f1a0e284`)
- Independent checker:
  `scripts/check_published_offwindow.py`
  (`6cf6493f688586c0ede49b9a78fe0f04c5fb2fca206834035259eb8bc4441420`)

## Claim ceiling and next gate

The certificate alone is independently replayed only through `k = 20`, but the
saturation statement itself is now proved for all admissible parameters in
Lean. The remaining route decision is to formulate a uniform
saturated-off-window structural transition. The `(4,6,6,3,2)` geometric state
is its first bounded falsification gate. A first certificate-free structural
bridge now compiles: the upper child, being larger than the classical `(3,6)`
threshold, contains a three-cap, and absence of a parent four-cap forces that
one cap's sweep interval to cover every lower-child vertex. The next contract
must consume or transport this covering-cap resource; the bridge alone is not
a parent cardinal bound.

A finite theorem that simply imports `decomposableStateUpper_466` would be
circular route evidence: it would close the smallest case with the certificate
whose uniform replacement is the research target.

## Preliminary route review and disposition

A first Sol audit used packet SHA-256
`5ea929b9570f6240368833758b05f82e215814abc783ceb03e42a73b9142a88a`.
It returned `partially_supported` at high confidence. It supported the uniform
Lean saturation proof and the bounded first gate, while correctly requesting
two cheap checks. The checker now directly replays greatest child indices as
described above, and Lean theorem
`published_saturated_auxiliary_alternatives_exclusive` explicitly proves that
the two saturation alternatives cannot both occur.

The audit's material remaining objection is strategic: one existential
covering cap is not yet connected to a family of retained-core or remainder
resources, and neither irreversible consumption nor ancestor-address nonreuse
has been defined. It proposes an explicit cap resource carrying slice
provenance, cap identity, tree address, coverage, transport, and port
ownership, followed by a bounded `(2,10)`/`(3,9)` falsification gate. This is
an advisory proposal, not a selected theorem contract. Claude Fable failed at
its provider quota before returning a review, so reciprocal consensus remains
pending on a corrected packet containing the two dispositions.
