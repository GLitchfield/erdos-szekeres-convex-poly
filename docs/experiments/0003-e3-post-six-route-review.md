# E3 post-six route-selection evidence

Date: 2026-08-03

## Decision to make

Choose the smallest next compiling Lean theorem that materially tests a
uniform proof of

```lean
∀ k ≥ 3, DecomposableExactUpperAt k
```

The decision is not whether endpoint/context language sounds plausible.  It is
which precise local or recursive statement should be attempted first, and what
bounded falsification check must precede or accompany it.

## Newly completed evidence

The previous reciprocal route review asked for the decomposable-signotope
bridge, the exact five-vertex base, an audit of the two six-vertex
off-diagonal states, and a proof-side lemma exposing the saturated boundary.
Since that packet:

- `IsDecomposableOn.turnSequenceAllowed` proves in Lean that every recursively
  deep-below coloring satisfies the rank-three one-change law.
- `decomposableExactUpperAt_five` compiles without using realizability.
- Kernel-checked LRAT certificates and semantic bridges prove the hereditary
  states `decomposableStateUpper_466` and `decomposableStateUpper_566`, together
  with their color duals.
- `decomposableExactUpperAt_six` now compiles.  Its proof reduces a hypothetical
  seventeen-vertex counterexample to those hereditary off-diagonal states.
- `make test` builds all 9,614 Lean jobs and passes 39 workflow tests.  The
  theorem's axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

These are finite milestones.  They do not prove any uniform recurrence and do
not establish that the intended context invariant is true.

## Established local structure

The failed scalar proof is pinned down by the compiling theorem
`published_induction_boundary_regression`: at `(a,u,k,u',a') =
(4,5,5,1,3)` its two claimed contributions total eight while the outer
threshold is seven.  The general Pascal-window absorption theorem compiles
only with the missing lower-endpoint hypothesis `k-a+1 ≤ u'`.

Across a recursive deep-below split, Lean now proves:

- a lower cup extends by an upper vertex exactly when that vertex lies to the
  left or right of the whole cup in sweep order;
- the dual statement for an upper cap and lower vertex;
- the two directional endpoint states are exclusive for an external vertex;
- if an `(r+1)`-cup is forbidden, every upper vertex is strictly straddled by
  every saturated lower `r`-cup;
- dually, if an `(r+1)`-cap is forbidden, every lower vertex is strictly
  straddled by every saturated upper `r`-cap;
- a strong polygon crossing the split is exactly a lower cup joined to an
  upper cap.

These statements are local to one split.  Nothing currently proves that a
finite endpoint/straddling summary is preserved through an arbitrary chain of
ancestor splits.

## Candidate next proof obligations

The reviewers should compare these as falsifiable theorem shapes, not assume
that any is true.

### A. Saturated singleton-anchor incompatibility

Prove the smallest lemma specialized to the regression: when one recursive
child is a singleton anchor and the sibling realizes the saturated cup/cap
state responsible for `(4,5,5)`, the anchor's forced straddling excludes the
extra boundary contribution.  The result should be stated directly using
existing `ContainsCupSet`, `ContainsCapSet`, endpoint, and deep-split
predicates.  This is deliberately local and may fail to compose.

### B. Rooted context state and one composition transition

Define a hereditary state carrying an external left/right anchor obligation
in addition to `(a,u,k)`.  Prove one root-split transition showing how the
obligation is consumed, strengthened, or passed to a child.  The state must
specialize to a statement that closes the `8 > 7` regression and must not
assume sweep realizability unless that assumption is present in the final
theorem.

### C. Minimal-counterexample root descent

Avoid defining a full recurrence initially.  Assume a smallest decomposable
counterexample to the uniform state theorem, expose its root split, and prove
that a saturated child plus the existing straddling lemmas either creates a
strong polygon or yields a strictly smaller rooted counterexample carrying an
explicit anchor condition.

### D. Endpoint-profile injection

Define left/right extension profiles and inject vertices or recursive blocks
into at most `2^(k-2)` profiles.  This would be closest to the desired final
count, but no current theorem shows that the profile is injective or
compositionally complete.

## Required discrimination

The selected next item must satisfy all of the following before it is treated
as the main route:

1. State every context parameter and quantifier precisely enough to translate
   into Lean without adding an oracle or an existentially chosen "good"
   decomposition.
2. Explain exactly how it closes the `(4,5,5,1,3)` regression.
3. Identify whether it composes under arbitrary `HasDeepBelowSplit` trees or
   is only a local diagnostic.
4. Give the smallest bounded exact search that could refute it, including the
   context recorded per coloring and an independent checker.
5. Separate an abstract decomposable counterexample, a signotope, and a
   straight-line realizable counterexample.
6. Name a redirect condition: a concrete failed transition or finite witness
   must send the project back to falsification or to a richer state.

The default experiment bound remains 30 minutes, 8 CPU cores, 16 GiB RAM, and
5 GiB under ignored `runs/`.  Reviewer agreement is advisory; the selected
theorem counts as progress only after it compiles in Lean.
