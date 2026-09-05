# Experiment 0116: what a child of a deep-below split sees, and the positional extremal tables

Date: 2026-09-05

Status: exact computation on the abstract decomposable class through seven
vertices, with the structural description verified on every split; no Lean
theorem is claimed.  Workstream B, step 2 of
`docs/plans/workstream-b-self-reliant-plan.md` (first level of the invariant
search).

## Question

The literal scalar induction for Baek–Balko's Theorem 8 fails at
`(4,5,5)`.  The working hypothesis of the plan is that the failure is an
external-endpoint effect that the child parameters `(a', u')` cannot see.
What exactly does a child of a deep-below split see of its sibling, and what
is the extremal function of the class under that information?

## The mechanism (derived from the four-vertex law, then verified)

Let `S = L ∪ U` be a deep-below split, `L` lower, `U` upper, interleaved in
sweep order; a mixed triple is a left turn exactly when its middle vertex is
in `L`.  Reading the mixed quadruples off this rule gives:

* A mixed quadruple with two vertices in each part is always strong.  A
  quadruple with three vertices in `L` and one in `U` is strong exactly when
  its `L`-triple is a left turn, wherever the `U`-vertex sits; symmetrically
  with the roles of left and right.  Hence a mixed set is strong exactly when
  its `L`-part is a cup and its `U`-part is a cap: **the strong sets of the
  union do not depend on the interleaving** (they are the strong sets of `L`,
  of `U`, and every cup of `L` joined with every cap of `U`).
* A cup of `S` is a cup of `U`, or a cup of `L` extended by one `U`-vertex on
  each side on which some `U`-vertex lies beyond it (`(x, a, a')` and
  `(a, a', x)` are left turns, `(a, x, a')` is a right turn).  Caps
  symmetrically: caps of `L`, or caps of `U` extended by `L`-vertices on the
  sides where `L` has vertices beyond the cap.

So the child `L` sees of `U` only (i) the longest cap `d` of `U` (through
strong sets, position-free) and (ii) the two gaps of `L`'s own sweep order
that hold the first and the last vertex of `U`: a cup `C ⊆ L` gains one
vertex on the left iff `first(C) ≥ g1` and one on the right iff
`last(C) < g2`.  Symmetrically for `U`.

Verification: for every decomposable coloring on `n ≤ 7` vertices (1, 1, 2,
8, 62, 718, 10,596) and every deep-below split of it (14,990 splits), the
longest cup, longest cap and largest strong set of the union computed from
the parts by the rules above agree with the values computed directly.

Two consequences recorded elsewhere: interleaving the two parts of a
single deep-below split never changes its strong sets, so a two-part
"Horton-type" interleaving is not a new test for the predecessor-half
conjecture (experiment 0115; with three or more parts the interleaving of an
inner split changes the cups and caps of the inner union, and through them
the strong sets of the outer union, so nested interleavings do give new
colorings); and Theorem 8's induction hypothesis must carry, per child, the
gap pair and the coupling parameter, not `(a', u')` alone.

## The positional extremal function

`E_low(a,u,k,c; g1,g2)` is the largest decomposable `L` with no `a`-cap, no
strong `k`-set, cups of length at most `c` (the strong coupling with a
sibling whose longest cap is `d = k − 1 − c`), and every cup `C` satisfying
`|C| + [first(C) ≥ g1] + [last(C) < g2] ≤ u − 1`; `E_up` is the mirror image
with caps.  Computed by brute force over the class (`n ≤ 7`); the column
`c = k − 1` (sibling without a cap, i.e. empty) is vacuous and omitted.
Entries are `(g1,g2) → E`; a gap `g` lies between vertex `g−1` and vertex
`g` of the child, so `g1 = 0` means a sibling vertex left of the whole
child.

| `(a,u,k)`, `T` | state | values |
|---|---|---|
| (4,4,5), 6 | `E_low c=2 (d=2)` | 3 at every gap pair |
| (4,4,5), 6 | `E_low c=3 (d=1)` | (0,0) 3, (0,1) 3, (1,1) 4, (1,2) 4, (2,2) 5, (2,3) 5, (3,3) 5 |
| (4,5,5), 7 | `E_low c=2 (d=2)` | 3 at every gap pair |
| (4,5,5), 7 | `E_low c=3 (d=1)` | 6 at every gap pair |
| (4,5,5), 7 | `E_up d=2 (c=2)` | 4 at every gap pair |
| (4,5,5), 7 | `E_up d=3 (c=1)` | (0,0) 4, (0,1) 4, (1,1) 5, (1,2) 5, (2,2) 6, (2,3) 6, (3,3) 6, (3,4) 6, (4,4) 6 |
| (5,5,5), 8 | `E_low c=2 (d=2)` | 4 at every gap pair |
| (5,5,5), 8 | `E_low c=3 (d=1)` | 7 at every gap pair |

`(5,4,5)` is the mirror image of `(4,5,5)`.  The `E_up` rows of `(4,4,5)`
mirror its `E_low` rows.

Reading: with a singleton sibling (`d = 1`, so `c = 3` at `k = 5`), the
child's extremal size depends on where the singleton sits.  At `(4,4,5)` a
singleton left of the child (`g1 = 0`) forces every cup of the child to
extend, so cups of length 3 are forbidden and the child is bounded by
`decomposableThreshold 4 3 5 = 3`; a singleton in gap 1 allows 4 vertices, in
gap 2 or 3 the full 5, and `5 + 1 = 6 = T(4,4,5)`.  So every extremal
`(4,4,5)` coloring with a singleton top split has the singleton strictly
inside the child, and the same holds for `(4,5,5)` on the upper side
(`E_up d=3`: 4, 5, 6 as the singleton moves inward, `6 + 1 = 7`).  The
scalar guess `decomposableThreshold(a, min(c+1, u − ext), k)` with `ext` the
number of sides on which every cup extends is wrong on 14 of the `(4,5,5)`
states and 20 of the `(4,4,5)` states, exactly the interior-gap ones.

Top-level closure holds tautologically (for every `(a,u,k)` with threshold at
most 8, the maximum of `E_low + E_up` over consistent interleavings equals
the threshold); this is a check of the mechanism, not of an induction.

## What this settles and what it does not

The state a profile-carrying induction must carry is now explicit at the
first level: per child, its own `(a,u,k)`, the coupling parameter, and the
two gaps.  Not settled: the recursion at deeper levels, where a grandchild
sees external vertices both above and below, strong sets chain across
levels (a cup of the lowest part, a cap of the middle part extended by the
highest part's vertices), and the state must carry both gap pairs and both
coupling parameters.  The next step is to define that two-sided state,
compute its extremal function from the class through `n = 8` or `9`, and test
whether it is closed under the split recursion (whether
`E(σ) = max E(σ_L') + E(σ_U')` over splits with the derived child states);
a closed state is the induction hypothesis for step 3, and the first failure
is the obstruction.

## Reproduction

```console
python3 scripts/decomposable_positional_extremal.py --max-n 7 --max-k 6 --output data/derived/decomposable-positional-extremal-n7.json
```

17 s single core.  Inputs: the class enumerator of experiment 0114
(`scripts/enumerate_decomposable_colorings.py`).
