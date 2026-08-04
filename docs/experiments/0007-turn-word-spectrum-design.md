# Turn-word pair-spectrum gate

## Status

Rejected as a uniform root congruence.  A targeted all-root replay found an
open seven-vertex counterexample at the required depth `d = k - 2`.  The
counterexample is now kernel-checked in `TurnLanguageCollision.lean`; every
census count below remains exploratory until independently replayed.  This
document does not select a uniform E3 route.

## Candidate state

Fix a triple coloring `χ`, a finite ordered vertex set `s`, and a depth `d`.
For each ordered pair `u < v` in `s`, let `L_d(u,v)` be the set of binary turn
words of length at most `d` realized by increasing vertex chains in `s` ending
at `(u,v)`.  The empty word is realized by the two-vertex chain.  Prepending a
vertex `w < u` appends `χ(w,u,v)` to a word in `L_d(w,u)`.

The pair-language spectrum is

```text
Σ_d(χ,s) = { L_d(u,v) | u < v and u,v ∈ s }.
```

Endpoint identities and multiplicities are deliberately forgotten.  If
`W_d` is the set of binary words of length at most `d`, then
`|W_d| = 2^(d+1)-1`, each pair language lies in `P(W_d)`, and the spectrum lies
in `P(P(W_d))`.  Thus the carrier is finite and depends only on `d`, although
this tower bound is far too large to imply the sharp `2^(k-2)` result.

This state retains correlations erased by monochromatic maxima.  In the
kernel-checked `k=6,n=9` pair-rank collision, the left upper child realizes
the word `left,right,right` on the chain `(0,2,3,5,8)`, ending at `(5,8)`;
the right child does not.  Direct exploratory recomputation finds that the two
spectra first differ at depth three.

## Rejected property-relative transition

At a fixed root partition `lower ∪ upper`, compare two decomposable parent
colorings with the same two child spectra.  The candidate assertion is not an
unconditional congruence.  It asks whether unequal parent spectra force a
strong `k`-set.  Equivalently, among parents avoiding a strong `k`-set, the
ordered pair of child spectra should determine the parent spectrum at depth
`d=k-2`.

The qualification is essential.  A first exploratory all-root replay through
eight leaves at `(k,d)=(5,3)` found 3,397 transition collisions overall, but
zero among the 5,624 root observations whose parent avoids a strong five-set.
Those open observations represented 2,952 distinct fixed-root inputs.

The first singleton-root `(k,n,d)=(6,9,3)` gate tested only one extreme root.
Repeating it at every singleton position refuted the apparent conclusion.
Roots `0`, `1`, and `7` had no open collisions, while roots `2` through `6`
and root `8` had 35,858 open transition collisions in total.  Each root had
85,797 open observations and 28,682 distinct child spectrum inputs.  Depth
three still separates the existing complete pair-rank witness, but that is
only a discriminator result, not a transition theorem.

More decisively, an all-root `(k,d)=(6,4)` replay found an open collision
already on seven vertices.  The root is

```text
lower = {0,1,2,3,4,5}, upper = {6}.
```

With triple bits ordered lexicographically on `Fin 7`, `1 = left`, the two
parent colorings are `0x76fbd6f54` and `0x76fbf6fd4`; their lower restrictions
are `0x6190644` and `0x61b06c4`.  Decomposition trees for the lower children
are

```text
((((5,3),0),(2,1)),4)
((3,(((5,2),0),1)),4).
```

The lower spectra agree separately at every depth from zero through four.
At depth four the parent languages differ at `(5,6)`: the first contains the
turn word `right,right,left`, while the second does not.  In the lower child,
that word prefix occurs at the incoming pair `(2,5)` only on the first side.
The second child has the same *global* language support at other endpoints,
which explains why forgetting endpoint incidence loses the transition.

## Review and bounded resolution

The bounded Sol/Fable review was run from revision `2d07250` before the
counterexample was found.  Both reviewers called the proposal only partially
supported and independently identified endpoint incidence and the untested
`k=6,d=4` gate as the cheapest falsification targets.  The subsequent replay
therefore exercised the proposal's own rejection rule.

One endpoint-incidence diagnostic records, for every vertex, the sets of
incoming and outgoing pair languages and then forgets the vertex identities.
Exploratory all-root replay of this state found no open transition collision
through eight vertices at either `(k,d)=(5,3)` or `(6,4)`.  At `(6,4)` there
were 153,648 open observations and 122,156 distinct fixed-root inputs, so the
gate was not injective.  At `(k,n,d)=(6,9,4)`, the same implementation then
tested every singleton root position: all 772,173 open observations passed,
with 56,615 child inputs at each position.  A smaller incoming-star spectrum,
which groups pair languages only by their common terminal endpoint, also
passes the currently covered gates in one exploratory implementation and
separates both known witnesses.  These results are diagnostic leads, not
evidence for a theorem.

Both mathematical reviews warn that repeated endpoint and edge refinement is
a Weisfeiler--Leman-style chase with no known round bound independent of the
number of vertices.  The completed formal package is consequently narrower:

1. Define bounded turn words and pair turn languages in Lean from increasing
   chains, together with a kernel-reducible recurrence.
2. Prove the structural recurrence for adjoining a new maximum singleton.  If
   every mixed triple `(w,u,z)` has color `c`, then the new language at `(u,z)`
   is the empty word together with `c` appended to the terminal incoming
   languages at `u`.
3. Kernel-check the seven-vertex witness: both trees are decomposable, both
   parents avoid a strong six-set, the lower spectra agree through depth four,
   and the parent spectra differ.
4. Audit for `sorry`, project axioms, unsafe code, and unverified decision
   procedures; run `make test` before committing.

`make test` passes for this package.  The theorem audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorry`, project axiom,
unsafe declaration, or external decision procedure in the proof.

## Stop and continuation rules

- The seven-vertex open collision rejects the plain spectrum as a root
  congruence.  Preserve it as a Lean negative theorem and do not add a general
  spectrum-composition assertion.
- Failure to separate the existing pair-rank collision rejects the semantics
  or implementation immediately.
- Any open collision for a proposed incidence state stops that refinement.
- Needing a second endpoint/edge color-refinement round stops the deterministic
  quotient route unless a fixed-round theorem is proved independently.
- A later uniform route requires a proof of the property-relative root
  transition and a compression/count theorem approaching `2^(k-2)`.  The
  finite tower bound alone is not progress on the sharp cardinality estimate.
