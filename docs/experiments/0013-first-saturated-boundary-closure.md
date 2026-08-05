# First saturated-boundary closure

## Question

Can the first feasible non-index-one published branch
`(a,u,k,a',u') = (4,6,6,3,2)`, with child sizes `(2,10)` or `(3,9)`, be closed
structurally without importing `decomposableStateUpper_466`, state 566, or a
finite certificate?

## Lean result

`ErdosSzekeres/StructuralChargingSaturatedResource.lean` proves the stronger
theorem `upper_card_le_eight_of_nonempty_lower_open_466`.

For any deep-below split with a nonempty lower child and a decomposable upper
child, if the parent contains no four-cap, six-cup, or strong six-set, then the
upper child has at most eight vertices. Consequently
`first_saturated_boundary_child_cards_impossible` eliminates both `(2,10)` and
`(3,9)` directly.

The elementary cup--cap symmetry now lives in the independent
`ErdosSzekeres/Duality.lean` module. Applying it gives
`lower_card_le_eight_of_nonempty_upper_open_646` and eliminates the reversed
child pairs `(10,2)` and `(9,3)` as well. Thus both color orientations of the
first gate are closed without importing a finite E3 certificate.

The proof uses no generated certificate and no consequence of the finite
state-466 or state-566 theorems.

## Mechanism

Choose any lower-child vertex `q`. An upper three-cap having `q` as a left or
right sweep endpoint would extend across the deep-below split to a parent
four-cap. Therefore no such endpoint three-cap exists. Every upper triple
entirely to one side of `q` must consequently be a cup, so the two gap sides
are ordered cup blocks.

Recursive decomposability supplies the one-change law on their union. The
previously proved symbolic `4+5/5+4` cup-block theorem then gives

```text
left.card + right.card ≤ 8.
```

The two gap sides partition the upper child because `q` belongs to the
disjoint lower child, giving the result.

The parameterized theorem
`gap_sides_avoid_cap_of_no_parent_succ_cap` extracts the uniform kernel: if a
parent avoids an `(r+1)`-cap, both upper gap sides around every lower vertex
avoid an `r`-cap. The special fact at `r=3` is that a three-cap-free set is
literally a cup block.

## Resource provenance

The same file also formalizes the more elaborate resource route proposed by
the preliminary Sol audit. A covering cap can be chosen inside an actual
published retained core, assigned its unique lowest separating-tree address,
and charged only to endpoint ports in that core. Identical cap witnesses
cannot receive different addresses. These declarations remain reusable, but
they are not needed to close the first gate.

## Claim ceiling and next gate

This closes the first `k=6` saturated off-window transition, not the uniform
all-parameter induction. For larger cap parameters, an `r`-cap-free gap side
is not simply a cup. The next structural question is whether recursively
decomposable `r`-cap-free gap sides admit a uniform two-block bound compatible
with the published Pascal allocation, or whether another state is needed.

A bounded reciprocal review should still audit the proposed higher-parameter
generalization before the Wayfinder route changes. Provider quota is not a
dependency of the Lean work: structural lemmas and falsification tests continue
while Fable is unavailable, and the missing review is recorded as such.
