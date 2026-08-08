# Experiment 0056: pivot-cone capacity

## Question

Can deep-below geometry close the first selected-core pivot overflow left by
pure source-child counting?

The scalar obstruction is the feasible `(a,u,k,a',u') = (4,8,8,3,4)`,
`10+13` split.  Ten lower vertices have nine adjacencies, so the coarse bound
permits nine hidden-lower pivots while the selected published upper core at
index three has only eight vertices.

## Result

Yes, and the proved statement is stronger than the frozen scalar gate.

For any deep-below split with a nonempty lower child, no parent four-cap and
no parent `u`-cup imply

```text
card (HiddenGapSource lower upper .right) < u.
```

The color-dual statement bounds hidden upper sources strictly by `a` under no
parent four-cup and no parent `a`-cap.  No sweep-realizability, strong-polygon
avoidance, child-cardinality equation, or saturation assumption is used.

At `u = k = 8`, the bound is at most seven.  Since
`decomposableThreshold 3 8 8 + 1 = 8`, every canonical pivot fits
simultaneously in an actual published upper core.  Lean constructs that slice
for every normalized upper child of cardinality thirteen.

## Mechanism

Let `q` be the minimum lower vertex.  Every canonical pivot of a hidden lower
gap lies in the upper child and strictly between two lower vertices, hence to
the right of `q`.  If three such pivots formed a cap, `q` would be a left
sweep endpoint of that upper cap.  The compiled deep-below endpoint-extension
lemma would then adjoin `q` to produce a forbidden parent four-cap.  Therefore
the entire pivot seed is a cup.  No parent `u`-cup makes its cardinality less
than `u`, and pivot injectivity identifies this with the number of hidden
sources.

This is a cone/link argument: one extreme vertex lowers the forbidden cap
parameter by one.  It is not additive endpoint slotting and does not use the
global recurrence.

## Lean evidence

`ErdosSzekeres/StructuralChargingPivotOverflow.lean` proves:

- the `10+13` equality normal form and source-adjacency bijection;
- the nine-distinct-interleaved-pivot skeleton implied by the coarse overflow;
- `hiddenLowerGapEnteringPivotSeed_isCupSet_of_no_cap_four`;
- `hiddenLowerGapSource_card_lt_of_no_cap_four_no_cup` and its color dual;
- the exact index-three threshold identities and uniform capacity bounds;
- `hiddenLowerGapSource_card_le_488_upper_core_capacity`; and
- `exists_publishedUpperPivotSlice_open_488_thirteen`.

All statements compile without `sorry`, `admit`, unsafe axioms, or an
external oracle.  The advisory innovation and adversarial reviews agreed on
the cone proof; Laplace independently compiled a scratch version.  Those
reviews are proposal evidence only—the repository theorem is the result.

## Disposition and next gate

The first geometry-sensitive pivot-capacity falsifier passes and the proposed
nine-versus-eight overflow is impossible.  The source-child adjacency bound
remains useful only as a normal-form diagnostic.

The next theorem-design target is the higher-index cone bridge.  For parent
cap parameter `a > 4`, the same anchor should make the pivot seed avoid an
`(a-1)`-cap.  To turn that into the required published-core capacity, the
proof must combine inherited decomposable/one-change structure on the pivot
seed with a general cup--cap bound and then match the resulting binomial
quantity to the selected child threshold.  That generalization is not proved
here.
