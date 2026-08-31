# Initial literature review: the exact Erdős--Szekeres formula

Last updated: 2026-08-30. This is a research synthesis, not a claim of
bibliographic exhaustiveness. The companion [source ledger](bibliography.md)
records the works actually checked. The search began from the 2000
Morris--Soltan survey and followed references and citations through the 2026
Baek--Balko paper, with targeted searches of arXiv, publisher pages, DOI
records, formal-proof repositories, and recent papers using the exact phrase
"Erdős--Szekeres conjecture". Empty, colored, higher-dimensional, and
convex-body variants were screened but retained only when they bear on the
exact planar formula or on formal proof methods.

## Exact target and current status

For `n ≥ 3`, let `ES(n)` be the least `N` such that every `N`-point subset of
the real plane in general position (no three points collinear) contains `n`
points in convex position. Erdős and Szekeres proved existence in 1935 and
conjectured

```text
ES(n) = 2^(n-2) + 1.
```

The statement has two logically independent halves:

1. **Sharpness/lower bound:** construct `2^(n-2)` points in general position
   with no `n` in convex position.
2. **Forcing/upper bound:** prove every `2^(n-2) + 1` points in general position
   contain `n` in convex position.

The lower bound is known for every `n`. The upper bound at that exact threshold
is known only for `n = 3, 4, 5, 6`; the case `n = 6` is `ES(6)=17` and was
settled by a large computer search. As of 2026-08-01, the all-`n` formula is
still explicitly described as open by Baek and Balko.

The best general asymptotic estimate is

```text
ES(n) = 2^(n + O(sqrt(n log n))).
```

Suk first changed the exponential base of the classical upper bound from
roughly `4^n` to `2^(n+o(n))`; Holmsen, Mojarrad, Pach, and Tardos improved the
error term. This almost determines the exponential growth but remains far from
the exact multiplicative threshold demanded by the conjecture.

## The proof landscape

### 1. The 1935 cup--cap argument

The original geometric proof orders points by their first coordinate and
classifies triples by orientation. It proves the exact cup--cap number

```text
C(a,b) = binom(a+b-4, a-2) + 1,
```

then derives

```text
ES(n) ≤ binom(2n-4, n-2) + 1.
```

This recurrence is highly formalizable: the essential objects are finite
orders, two colors/orientations on triples, and path-extension ranks. It is not
by itself sharp for convex `n`-gons because a convex polygon can be assembled
from a cup and a cap sharing endpoints; simply forcing a cup or cap loses the
structure needed for the `2^(n-2)+1` threshold.

### 2. The lower-bound construction

Erdős and Szekeres later gave recursive point sets of size `2^(n-2)` avoiding a
convex `n`-gon. The construction separates two smaller configurations so
strongly that every cross-line has a prescribed above/below relation. Modern
"decomposable" point sets generalize this pattern. This is the cleanest first
all-`n` theorem for Lean: it proves the exact formula cannot be improved and
forces us to formalize the same separation operations that appear in current
structural work.

Formalizing only the lower bound does **not** solve the conjecture. It should be
labeled a formal reproduction of a known theorem.

### 3. Incremental upper-bound improvements

Chung--Graham removed the `+1` from the 1935 binomial upper bound.
Kleitman--Pachter obtained a further linear subtraction, and Tóth--Valtr proved
the explicit bound `ES(n) <= choose(2*n-5,n-2)+2`, cutting the leading binomial
expression by about a factor of two.  Their proof selects a convex-hull vertex,
uses an exterior segment and projective transformation to preserve finite
convex-position judgments, and makes every cap on the remaining points extend
through the selected vertex before applying the usual cup--cap theorem. Vlachos,
Norin--Yuditsky, and Mojarrad--Vlachos improved constants further. These papers
develop useful notions of convexity witnesses and forbidden subconfigurations,
but none changed the exponential base.

The Tóth--Valtr bound is now reproduced in Lean as
`ErdosSzekeres.tothValtr_upper`, with the exact threshold
`choose (2*n-5) (n-2) + 2`, and its strict improvement over the repository's
classical binomial threshold is also proved for `n >= 4`.  The formal proof
constructs the projective normalization explicitly and proves orientation-sign
and finite-subset convexity preservation.  This closes the project's
supporting quantitative milestone `Q-UPPER`; it does not improve the known
mathematics or reduce the open exact upper-bound edge.

Suk's 2017 JAMS paper introduced the decisive positive-fraction/partition
method, obtaining `2^(n+O(n^(2/3) log n))`. Holmsen--Mojarrad--Pach--Tardos
sharpened this to `2^(n+O(sqrt(n log n)))` and extended the method to
pseudoline arrangements and convex bodies. The exact formula likely needs a
structural ingredient not visible after the losses inherent in these density
and partition estimates.

The current arXiv v3 and JEMS source for the Holmsen--Mojarrad--Pach--Tardos
argument were reauthenticated on 2026-08-16.  Its first distinctive Euclidean
layer is exact and finite: on each spike pool it defines a vertical
triangle-containment order and a horizontal crossed-segment order, proves that
every distinct pair is comparable in exactly one order, and immediately uses
Dilworth to obtain `|P_i| <= v_i*h_i`.  The repository's support-region data
already supplies the local point-set hypotheses and its triangle order is the
reverse vertical order.  This first layer now compiles in Lean with the literal
closed-segment definition: an explicit Cramer bridge proves the horizontal
order laws, the two anchor-orientation signs give exact four-way exclusive
comparability, and an independent finite theorem constructs maximum chains and
derives the product bound.  A rational permutation-2143 spike fixture has
Greene shape `(2,2)` and saturates the product, so the two common projective
rankings alone do not improve its coefficient.  One raw input to the next
gluing layer now compiles as well.  For a strict vertical pair in the left
spike, Lean derives negative orientation at the actual outer-right anchor and
at every point of the adjacent right spike; the reflected right-pair theorem
derives both positive signs at the outer-left anchor and adjacent left spike.
These are point-set consequences of the raw support regions and general
position, not supplied support certificates.  The mixed-four-subset gluing
consumer now compiles as well.  Lean proves the selected right-anchored chain
of one spike and selected left-anchored chain of its neighbor jointly convex:
the actual `x3` and `x1` caps handle the two `3+1` directions, opposite-pair
support handles `2+2`, and the profile caps handle the unmixed subsets.  No
common-anchor or supplied convex-union certificate appears.  The corrected
cyclic source projection now compiles at the sharp reachable endpoint
`3 <= r`, preserving the original carrier through cell zero and the final
wrap.  The complete local vertical-profile producer also compiles: it derives
the reversed HMPT/Suk order semantics, transitive coloring, actual maxima, and
the exact binomial profile bound internally from one raw region.  The cyclic
no-target consumer now compiles as well.  It chooses one produced profile in
every source pool, aligns the final-to-zero successor window, applies the
distinct-anchor gluing theorem, and converts each exact disjoint-union
cardinality into the published adjacent-chain inequality on the unchanged
carrier.  Thus C1--C4 formalize H2 and reduce the remaining finite-layer count
from five to four.  The source-authenticated H3 layer now compiles as well.
Lean derives literal inner/outer five-point semantics and both-color
transitivity from raw horizontal geometry, then constructs actual maximum
literal inner and outer subchains of the unchanged H2 horizontal chain and
proves `h_i <= choose (c_i+d_i-2) (c_i-1)`.  This reduces the remaining
finite-layer count from four to three without importing the H4 whole-chain
convexity or parity-gluing statements.  The source-authenticated H4 layer now
compiles too: both literal local chains are convex; same-parity remote pair and
base-edge separation is derived around the full cycle including `r=3` wrap;
each parity union of inner chains is convex; and one dependent package retains
the exact H2/H3 profile family together with all adjacent, outer, parity-inner,
and total-inner no-target inequalities.  H5 aggregation now compiles as well.
Lean proves the conservative natural-number binomial estimates and combines
the exact stored H2--H4 family with the source support-product inequality,
including cyclic exponent reindexing, ceiling cover, positive root
  cancellation, and one-bit strict slack.  The finite-layer count is therefore
one.  H6 now compiles as well.  The exact natural scale
`max 3 (Nat.sqrt (n * Nat.clog 2 n) + 1)` supplies the square and ceiling
covers, and the endpoint composes the source and H5 on the unchanged carrier.
For every `n >= 3`, Lean proves
`ForcesConvexPolygon n (2^(n + 32*Nat.sqrt (n*Nat.clog 2 n) + 128))`.
This completes the point-set reproduction of the HMPT published asymptotic
order.  It does not improve that order and does not cover the paper's broader
pseudo-configuration variants.

The finite layer of Suk's proof is now formalized separately from those density
losses.  Lean proves the finite chain--antichain threshold, the
triangle-containment partial order, the adjacent-cap gluing theorem, and the
local support-to-certificate geometry.  Raw support-region signs now also
produce the exact two-color semantics, transitivity, and convexity of the whole
anchor-extended selected chain.  The exact adjacent-pool recurrence, its
indexed chain-rich iteration, and the finite path dichotomy between separated
antichain-rich pools and a consecutive chain-rich run compile as separate
theorems.

The primary Pór--Valtr construction requires a rounding correction that is
easy to lose in a prose summary.  On journal p. 629 the open region contributes
`ceil (N / 2^(32*r)) - 1` interior points; the full ceiling is reached only by
adjoining the boundary anchor.  Lean now proves an explicit large-parameter
lemma absorbing that one-point loss.  The literal unchanged-coordinate
x-sorted extraction is false, but a source-faithful cyclic replacement does
compile: marked-edge block selection and strict-cap support contraction produce
`r-3` raw consecutive support pools without cardinality loss.  A global Lean
theorem then applies the local Dilworth alternative to every pool and returns
actual witnesses for one of the two global branches.  Both branches now have
compiling consumers: actual chain runs feed the adjacent-pool recurrence, while
pairwise nonadjacent actual antichains yield internally selected base-supported
caps whose full union is proved convex.  Their disjunction is eliminated by a
single finite theorem under explicit cardinal hypotheses.  On the source side,
Lean also constructs a clockwise periodic strict-cap enumeration of any
supplied finite convex general-position set without changing its carrier.
Lean now also formalizes the remaining Pór--Valtr source count: an ordered
alternating support satisfies the exact cyclic open-cell product inequality,
at least half the cells meet the corrected ceiling-minus-one threshold, and
all marked pools are packaged on the original input carrier.  An independent
review checked the source signs, wrap, rounding, factorial cancellation, and
carrier boundary.  The positive-fraction parameter composition and asymptotic
assembly now compile too.  For every `n >= 65`, Lean proves the exact bound

```text
ES(n) <= 2^(n + 64*(sukCubeScale n)^2*clog_2(3*n) + 128),
```

where `sukCubeScale n` is the least natural `s` with `n <= s^3`; a separate
certificate bounds the cube of `s^2` by `64*n^2`.  This is a conservative
formal realization of Suk's `2^(n+O(n^(2/3) log n))` method, not a reproduction
of its optimized constant and not progress on the exact threshold.  The
stronger Holmsen--Mojarrad--Pach--Tardos point-set order now compiles too.  Its
H1--H6 modules prove the explicit bound
`2^(n + 32*Nat.sqrt (n*Nat.clog 2 n) + 128)` for every `n >= 3`, thereby
reproducing `2^(n+O(sqrt(n*log n)))`.  This is a formal reproduction of the
published order, not an improvement and not progress on the exact threshold.

### 4. Equivalent strengthened statements

Erdős, Tuza, and Valtr introduced numbers `N(n,a,b)` that simultaneously avoid
an `n`-gon, an `a`-cap, and a `b`-cup, conjecturing an exact binomial-sum
formula. Crucially, their family of statements is equivalent to the classical
Erdős--Szekeres conjecture through a monotonic implication scheme. Jineon Baek
proved the first genuinely new case, `(n,4,n)`, in 2025 and formalized the
combinatorial proof in Lean 4.

This is more than a neighboring variant: it offers both an equivalent ladder
toward the target and the most directly reusable Lean infrastructure located
in this survey. However, proving isolated low-`a` cases does not automatically
reach `(n,n,n)`; the implication directions and parameters must be tracked
precisely.

### 5. Abstract configurations, SAT, and realizability

Replacing a point set by its ordered triple-orientation data makes the problem
finite and friendly to SAT and Lean. It also creates a major correctness trap.
Peters and Szekeres proposed a stronger set-theoretic/ordered-hypergraph
generalization. Balko and Valtr used SAT to refute that abstraction for the
relevant larger cases. Thus a theorem about arbitrary two-colorings or even a
locally transitive triple system need not prove a theorem about planar points;
realizability and global orientation axioms matter.

Fukuda, Miyata, and Moriyama's complete enumeration of small realizable
oriented matroids supplies an exact final-polynomial obstruction for the unique
uniform nonrealizable rank-three class on nine elements.  The archived official
59-row certificate and the independent Java Oriented Matroids Ringel example
have been reconciled to one frozen 84-sign representative.  The project now
formalizes the bracket identity, reorientation and relabeling transport, all
59 strict certificate inequalities, and the balanced final-product
contradiction in Lean.  Thus
`ringelNine_not_rankThreeVectorRealizable` and its sweep-realizable and
decomposable-restriction exclusions compile.  This is a local obstruction, not
a characterization of realizable sign systems: it affects the main proof only
after a separate theorem forces a Ringel restriction from a retained
full-context hypothesis.  A corrected exhaustive replay finds 67 Ringel
restrictions in one family-layer state-567 SAT assignment.  That is useful
model evidence, not a producer theorem; the assignment does not satisfy the
stronger shape/coverage layer, and one example cannot justify uniform minor
selection.

The right-extension-fiber audit also separates three notions that the project
must not identify.  Finschi--Fukuda's account of Las Vergnas localization gives
an exact coline-cycle characterization of uniform *abstract* one-element
oriented-matroid extensions.  Bergold--Felsner--Scheucher similarly construct
rank-three signotope extensions from lower sets in the crossing order.  These
are pseudoline or abstract-extension statements, not straight-line
realizability criteria.  For one fixed vector realization,
Sturmfels--Ziegler describe extensions through the face poset of a realizable
adjoint; the union over all realizations is a different object, and topology or
connectivity of the full abstract extension space does not decide membership in
that realizable union.  Padrol--Philippe further distinguish sweep data from
the little oriented matroid/order type, while Miyata's representation of the
related rank-three sign systems uses pseudocurves.  Consequently, cocircuit
localization, crossing-poset lower sets, and extension-space connectivity are
useful abstract normal forms but currently supply no noncircular
characterization of the project's `GeometricRightExtensionFiber`.  A fixed
coordinate fiber is instead a strict half-plane feasibility problem; planar
Helly applies only while all constraints share that one realization.

Marić's paper reports an Isabelle/HOL formal proof of `ES(6)=17`.  A local
source audit identifies Szekeres--Peters's eight four-sign `E*` patterns with
the project's `TurnSequenceAllowed`/`OneChangeOn` convention and separates
their consecutive cup--cap convex-six predicate from the repository's
strong-polygon predicate.  The official `HappyEnding.zip` was retrieved and
audited on 2026-08-15, but its checked theories stop at cases through five;
the `6/17` instance appears only as dormant generator input, and the archive
contains no license, session root, generated formula, proof artifact, or final
six-point theorem.  The public planar presentation and lower bound are already
formalized, but no external six-point theorem has been admitted into Lean.
Recent SAT work on 33 points (`n=7`) is currently a preprint/encoding effort,
not a proof of `ES(7)=33`. Any future SAT route in this repository must produce
a certificate checked inside or reduced to Lean's kernel and must separately
verify the geometric abstraction.

### 5a. A nested-hull partial result for hexagons

Dehnhardt, Harborth, and Lángi prove that every seventeen-point
general-position set with a pentagonal outer hull contains a convex hexagon.
Their first lemma is more reusable than that fixed statement but has important
literal hypotheses: a convex core `Q` lies strictly inside one convex polygon
`P`, and the selected points are vertices of `P` lying beyond exactly the same
edge of `Q`.  Under those hypotheses the core vertices together with the
selected outer vertices are in convex position.  Consequently, in a carrier
with no convex `r`-set, a same-edge bucket around an `s`-vertex core has at
most `r-s-1` outer vertices.  This parameterized cap is an elementary
corollary of the source lemma, not a theorem stated by the paper.

The paper's second lemma avoids a single-core coverage assumption by using a
cyclic family of triangles, quadrilaterals, and pentagons whose exposed edges
cover an enclosing polygon.  Summing the corresponding bucket caps proves its
fixed-six criterion.  The construction is potentially useful nested-hull
machinery, but the paper does not produce such a family from an arbitrary
point carrier or connect its shell count to a half-sized predecessor-free
support.  Interior points and points beyond several edges also remain outside
the single-core bucket system.  Thus these lemmas are source-authenticated
conditional structure, not a new exact upper bound or a completed destination
dependency.

### 6. The 2026 structural advance

Baek and Balko introduced split `k`-gons, proved that the conjectured threshold
`2^(k-2)+1` is exactly right for this relaxation, proved the original
Erdős--Szekeres conjecture for decomposable point sets, and supplied new
extremal constructions generalizing all earlier known ones. They also showed
that a corresponding ordered-hypergraph generalization fails.

For the exact conjecture, the key consequence is a reduction in the shape of a
possible counterexample: the known recursive/decomposable world already obeys
the formula. A successful proof must either show every minimal extremal
configuration has enough decomposition, or control the genuinely
indecomposable remainder. Formalizing this theorem would create a precise Lean
definition of that obstruction and is a strong candidate for an early major
milestone.

The first part of that milestone now compiles in
`ErdosSzekeres.Decomposable`: arbitrary deep-below partitions (including
parts interleaved in sweep order), recursive decomposability, hereditary
closure under nonempty subsets, and the lemma combining a cup in the lower
part with a cap in the upper part into a strong polygon.  The exact
counterexample predicate and the formal E4 implication from the decomposable
upper theorem to indecomposability also compile.

The converse realizability direction for this formal recursive model now
compiles in `ErdosSzekeres.DecomposableRealization`.  Keeping each abscissa
equal to its global sweep index, a finite vertical-shift argument merges two
child ordinate realizations even when their index sets interleave.  Lean then
proves `IsDecomposable.isSweepRealizable`: every abstract coloring in the
repository's recursive class is induced by a planar point configuration in
general position.  This is a theorem about the repository model, not a claim
that every signotope or every ordered-hypergraph decomposition is realizable,
and it does not prove that the same decomposition tree satisfies the stronger
coordinate predicate `IsGeometricallyDeepBelow` or prove the Baek--Balko
cardinality bound.

The binomial-window cardinality induction proving the exact threshold remains
E3; it is not yet claimed by the repository.  A literal transcription of the
new journal proof fails at the auxiliary boundary
`(a,u,k,u',a') = (4,5,5,1,3)`: the two contributions total eight although the
outer threshold is seven.  This finite arithmetic fact is checked in Lean by
`published_induction_boundary_regression`.  It identifies a gap in that proof
step, not a counterexample to the decomposable-set theorem itself.  The
formalization therefore records the published threshold and its diagonal
identity but requires a corrected invariant or boundary lemma before claiming
E3.

The source semantics of that auxiliary choice are now formalized in
`PublishedInductionSemantics.lean`. The parameter is chosen maximally from the
actual child cardinality, and the proof retains an actual subset of child
vertices. Lean proves the associated complement inequality and the uniform
fact that auxiliary index one forces the entire child to be a singleton. The
specific `(4,5,5,1,3)` branch therefore reduces to the existing
certificate-free singleton-root theorem and now has a compiling sharp bound
of seven. Other off-window auxiliary indices remain unresolved, so this closes
the first regression rather than E3.

The full journal text has now been inspected directly.  Its final two-sum
calculation contains the same defect: when an auxiliary parameter falls below
the active Pascal window, the proof retains the next classical cup--cap term
but then treats it as if it belonged to an empty interval.  Lean separately
checks `decomposableBinomialWindow_diagonal_pair_le`, showing that the outer
diagonal split is sound and that the defect is introduced only by a recursive
off-diagonal state.  No correction or replacement proof was found in the
published sources as of 2026-08-01.

The first correction layer now compiles.  Lean proves the published
Pascal-window absorption in its valid interior range and proves the missing
arbitrary-split geometry: a crossing strong polygon has exactly a cup on its
lower side and a cap on its upper side, while a crossing cup (respectively,
cap) uses at most two upper (respectively, lower) sweep endpoints.  These
vertices are proved pointwise to be actual extremes of the full chain.  These
lemmas show why the scalar threshold induction loses information at the
boundary and identify endpoint-aware chain profiles as the next invariant.

The endpoint profile has now been refined to an exact one-vertex transition.
For a nonempty cup contained in the lower block, Lean proves that inserting an
upper-block vertex gives a cup if and only if the new vertex is to the left or
right of the whole old cup in sweep order; the dual statement holds for caps.
The two directional alternatives are disjoint for a vertex outside the chain,
and cardinal corollaries turn either flag into a chain-size increment.  In the
negative direction, forbidding that increment forces the opposite vertex to
be strictly straddled by the chain.  This supplies the local state machine
needed by a repaired E3 proof, but the global injection/count of endpoint
profiles is not yet proved.

An exact all-root census has now tested how far those local states compose.
Through eight leaves, independent implementations agree on every compatible
root, every fixed-ambient restriction, and every anchor/four-chain relation.
Directional maxima at one gap, or even at all anchors supplied by the sibling,
do not determine the parent profile.  A complete all-gap word survives only
the `k = 5` boundary: at `k = 6`, `n = 9`, an independently checked pair of
decomposition trees has identical child all-gap maxima profiles and different
open parent profiles.  Hence a uniform proof must retain correlations between
chains—such as predecessor/rank downsets—or prove a new bounded quotient; a
maxima-only context recurrence is insufficient.

A bounded 2026-08-13 literature pass strengthens that redirect without proving
a new theorem.  The closest exact published architecture attaches extension
ranks to ordered pairs, generates a down-set or monotone word at each vertex,
proves injectivity by a local extension contradiction, and classifies the few
missing profiles.  In the split-polygon application the cap and cup share one
endpoint, while synchronizing the other endpoint remains the critical gap.
The repository's `RankProfile` definitions already express the pair-rank and
down-set layer, but `RankProfileCollision.lean` proves that the complete clipped
child pair-rank matrix is not a recursive congruence even for explicit rational
realizations.  The resulting proposal is therefore a *full-ambient* generated
down-set/endpoint-repair child under `FP-01`, first tested against that Fin9
collision.  The published split theorem is motivation and source material, not
an imported Lean premise; abstract OneChange and decomposable instances remain
controls for a sweep-realizable uniform target.

## Convex-geometry beta-transform screening

Edelman, Reiner, and Welker study convex and free sets of oriented matroids and
express a beta invariant of the convex-set lattice as an alternating weighted
sum over free sets. For a planar point configuration, a free set is a
convex-position subset whose hull contains no other point of the restricted
configuration. This makes a hereditary restriction sum potentially relevant:
for a fixed convex subset `A`, precisely the points outside `conv(A)` may be
chosen freely in a restriction containing `A`.

The source does not prove an Erdős--Szekeres inequality, and its application
section has a sign defect that matters before that idea can be tested. It
states that the alternating free-set sum is `(-1)^(rank-1)` times the number of
interior elements, while the preceding interior-link sphere has dimension
`rank-2`. On four general-position planar points with one interior point, the
free singletons, pairs, and triples contribute `-4 + 12 - 9 = -1`, not the
displayed rank-three value `+1`. The corresponding hereditary polynomial is
`-z^4`, so a cone treating those coefficients as nonnegative is not the
published free-set sum.

Ticket 0063 consequently keeps the proposed beta transform outside the
frontier portfolio. This is a defect in the frozen sign convention, not an
exhaustion of the machinery. A future card must prospectively choose either
the nonpositive free-set enumerator or its consistently negated positive
interior enumerator, pass the four-point control, and undergo fresh route
review before larger controls or rational cones are run.

That prospective correction was later made and admitted as `FP-19`. Independent
implementations agree on `betaPlus = -betaMinus = interiorCount`, the exact
four-point control, and all frozen larger transforms. The first
cardinality-only cone at `(n,k)=(9,5)` is nevertheless exactly feasible. This
retires the aggregate cardinality-cone subfamily before `(17,6)`; it does not
refute the hereditary identity or independently sourced incidence/realizability
machinery. No such richer producer is currently admitted.

## Canonical bowtie decomposition screening

Bouvel, Féray, Goaoc, and Koechlin define a bowtie product of two acyclic
uniform rank-three chirotopes with marked proxies. For nontrivial factors, the
product is a chirotope exactly under the source's extreme-proxy condition; its
realizability and extreme elements are characterized, and every chirotope has
a unique canonical decomposition tree whose nodes are convex or indecomposable
and whose edges never join two convex nodes. The full arXiv v2 and official
SoCG 2024 versions were cross-checked on 2026-08-22; their titles and theorem
numbers differ.

The source does not prove Batch011's proposed three-term maximum formula for
the convex capacity of every restriction, nor does it identify the project's
`HasProperDeepBelowSplitOn` predicate with a bowtie edge after restoring
proxies. Factor-recovery statements also do not cover every empty or singleton
boundary restriction automatically. The idea therefore remains a
source-authenticated structural proposal with a short consumer ladder, but no
exact fixture, boundary calculus, or project adapter is dispatch-ready.

## One-interior alternating-wedge screening

Huemer, Hurtado, Noy, Urrutia, and Wood define a signed alternating count of
convex polygons containing exactly one interior point and localize it at a
directed edge. In the 2022 version of record, the local value lies in
`{-1,0,1}`; it equals `+1` exactly when every other point lies in the interior
of the opposite `p`-wedge. The global identity counts non-extreme points. The
source gives neither an exact-threshold positive-incidence theorem nor a
two-block decomposition of the occupied wedge.

Batch011 proposed splitting that wedge by a ray from `p` toward edge `qr`.
Primary-source geometry exposes a definition defect: such a ray enters the
triangle sector, while the `p`-wedge is the opposite sector; the edge also does
not choose a unique direction or boundary policy. A corrected divider would be
a new prospective project definition, and positive-incidence production plus
the deep-split adapter remain separate speculative steps. The current gate is
therefore not executable, though the authenticated local charge remains useful
search information.

## Operadic Gröbner screening

Dotsenko and Khoroshkin develop Gröbner bases for shuffle operads using
decorated tree monomials. Their exact source defines admissible path-
lexicographic orders, subtree divisibility, reductions and S-polynomials,
proves the operadic Diamond/Buchberger criterion, identifies irreducible tree
monomials as a quotient basis under the Gröbner hypothesis, and explains how
symmetric operads and ideals pass to the shuffle setting. The machinery begins
with a declared generator collection, composition law, monomial order, and
relations; it does not manufacture those data for an unrelated combinatorial
model or guarantee finite completion.

Batch 013 proposed identifying decomposable sweep-coloring witnesses modulo
equality of their truth tables through four leaves plus endpoint flags. The
source audit finds the transfer incomplete at the first semantic hinge. A
rewrite inside an outer decomposition tree can create triples with leaves both
inside and outside the replaced subtree. Those mixed triples are absent from
the local table, and the current sweep-endpoint predicates are not a complete
boundary interface. Closure of an already defined operadic ideal under
substitution therefore cannot establish the missing project evaluation
morphism or contextual congruence.

The same card's finite normal-form gate also cannot test its advertised live
states at eight leaves: the exact project thresholds are 14 at `556`, 25 at
`567`, and 41 at `578`. This expires only the literal B013-S02 representation
and gate. A materially different operadic approach remains possible only if it
first defines a typed evaluation and proves a complete outer-context
congruence independently of any overlap census or desired capacity bound.

## Mutation connectivity and the Layer-F boundary

Roudneff and Sturmfels prove that general-position arrangements can be joined
by representability-preserving mutations. This is relevant to the proposed
Layer-F normalization because a single rank-three mutation changes one
oriented triple while remaining realizable. The theorem is unrestricted,
however: it does not say that the induced graph on configurations avoiding a
fixed strong polygon is connected, or that every such component contains a
decomposable configuration. Removing the target-containing vertices and
edges can create local minima or disconnected components. Consequently the
project still needs an explicit target-free descent or a component theorem;
ordinary mutation connectivity cannot serve as the missing normalization.
See Roudneff--Sturmfels (1988), DOI `10.1007/BF00151346`, rechecked
2026-08-10.

## Anti-exchange closure and directed modular-decomposition screening

Edelman's 1980 theorem identifies finite anti-exchange closure systems with
meet-distributive closed-set lattices. That theorem does not identify the
binary projection sending a rooted planar circuit `(p; {a,b,c})` to three arcs
`p -> a,b,c` with a named lattice join-dependency relation. McConnell and de
Montgolfier's directed modular-decomposition theory starts from an already
specified digraph and then canonically organizes its strong modules; it cannot
supply the missing closure-to-digraph identity.

This matters geometrically. Collapsing rooted circuits to simple arcs forgets
which three hull labels occurred together, while convex 2|2 circuits do not
appear in point-convex closure at all. The projected graph therefore loses
orientation information used by `HasDeepBelowSplit`. Its canonical module tree
also need not canonically choose one shore of a cut. Continuous Batch009's
closure-factor seed consequently remains source-and-consumer grounding: a
primary rooted-circuit/join-dependency correspondence, an orientation-return
theorem, and a recursive numerical consumer are all still missing.

## Dulmage--Mendelsohn source screening

Dulmage and Mendelsohn's 1958 paper gives the original finite simple bipartite
covering framework, maximum disjoint edge sets, irreducible pieces, canonical
decomposition, and minimum-cover lattice. Kita's 2016 primary preprint gives a
modern component-poset formulation: for ordinary matchings it defines
elementary components, their canonical partial order and normalized ideals,
and later supplies an alternating orientation and side-sensitive reachability
from vertices loose under maximum matchings.

The two sources close several remembered-definition gaps but do not yet give
one exact proposition matching the project's intended chosen-maximum-matching
auxiliary implementation to the classical elementary-component partition in
all inevitable-edge cases. Explicit isolated, edgeless, perfect-matching, and
parallel-edge conventions also remain only partially covered. More
importantly, neither source defines the project's proposed role layers,
boundary map, common-ideal selector, geometric return, or recurrence consumer.
The typed-DM proposal therefore remains a source-grounding lead, not an
authorized computation or movement on the exact proof.

## Split decomposition and the complete segment-crossing graph

Gioan and Paul give a source-faithful graph-labelled-tree formulation of split
decomposition for connected graphs. In that domain, original graph vertices
are tree leaves, auxiliary marker vertices label internal incidences, internal
tree edges induce leaf bipartitions, and a reduced tree has prime or
clique/star-degenerate internal labels with stated join prohibitions. Their
uniqueness theorem is explicitly for connected graphs; an arbitrary split
inside a degenerate node may also require a node split rather than already
appearing as a reduced-tree edge. Cunningham's accessible official record
supports a general unique digraph decomposition at abstract level but does not
authenticate the exact undirected disconnected conventions needed here.

This domain restriction is decisive for the Batch011 segment-crossing seed.
Its vertices are all labeled point-set segments, adjacent exactly when two
disjoint-endpoint segment interiors cross. Every convex-hull boundary segment
is isolated, so this graph is disconnected for every nontrivial planar input.
Deleting those vertices changes the proposed endpoint-purity statement, while
passing to the complement is not justified by a split-preservation theorem.
No located source defines a unique disconnected tree or forest retaining all
original leaves and the required marker, reduction, component, and boundary
semantics. Endpoint-pure point-cut uniqueness and the geometric return to a
deep split are separate missing results. The route therefore remains
source/definition grounding rather than an authorized graph experiment.

## Matroid foundations and marked extension-fiber images

Baker and Lorscheid represent realization classes and rescaling classes using
universal idylls and matroid foundations. Baker--Lorscheid--Zhang further show
that an embedded minor `N -> M` induces a foundation morphism `F_N -> F_M`.
For a child matroid and its deletion parent, precomposition therefore gives a
well-defined unmarked map from child to parent rescaling classes, with fixed
underlying matroids.

That statement stops before the geometry needed by `FP-13.D`. The project's
right-extension fiber fixes an oriented extension link, restricts to positive
rescaling/sign data, marks an affine direction and a rightmost element, and
takes a union over all sweep-compatible real realizations of the parent. The
located foundation sources neither define this marked domain nor prove that
its deletion image is a finite-atlas constructible or semialgebraic region;
they also do not identify that image with the project union fiber. Such a
bridge may be derivable using additional real-algebraic machinery, but it is
not supplied by the authenticated propositions. Foundation elimination is
therefore premature until the marked-image and union-equivalence theorem is
sourced or proved independently.

## Circular-ones representations and negative certificates

Hsu and McConnell define the circular-ones property by a cyclic column order
making every row's ones consecutive, equivalently its zeros consecutive. Their
PC tree compactly represents the complete family of compatible cyclic orders;
prime-node reversals and circular equivalence account for its embeddings, and
their incremental reductions construct the representation on successful
instances.

Safe supplies the missing negative-side theorem, with a correction to the
seed's terminology. His explicit family `FcircR` is a minimal family of
minimal forbidden submatrices for the circular-ones property. Lemma 10 carries
a Tucker matrix in a row-complement reduction back to row/column maps in the
original matrix, and Corollary 14 plus Algorithm 1 find an `FcircR` member in
the original negative instance in linear time. This is a replayable negative
certificate. It is not necessarily a Tucker matrix, and the source does not
claim that the occurrence is unique, implementation-independently canonical,
or minimum-cardinality among all obstructions in the input.

The project audit has now fixed the prospective complete strong-five incidence
matrix, one deterministic compatible original-label cyclic-order selector, and
the alternating-position implication at `k = 6`. Every circular interval of
five positions contains both parities even on an odd carrier and across the
cyclic seam, so a positive matrix conditionally supplies the literal
`StrongPredecessorBicoloringAt 6` conclusion. The first remaining finite-audit
gap is an input package: the available receipts do not freeze complete
unchanged same-tier colorings, all strong-five rows, a realized-control
catalogue, and independent-checker inputs for the advertised panel. No matrix
or fixture outcome has been computed under this route. More importantly, even
finite positive outcomes would not prove the uniform circular-ones producer
for every admissible strong-six-free realizable coloring.

## Finite-algebra decomposition versus a middle-link invariant

Rónyai and Eberly--Giesbrecht provide general algorithms for radical and
semisimple decomposition of finite-dimensional associative algebras over
finite fields. The official Wedderga manual gives a concrete semisimple
group-algebra setting and explicitly records nonuniqueness of complete
orthogonal primitive idempotents; Zhu treats lifting central idempotents across
Jacobson radicals as a separate hypotheses-sensitive problem. These sources
support generic machinery, not the proposed geometric representation.

The Batch010 middle-Wedderburn seed fails before that machinery applies. A
project `TripleColoring` returns `Turn`, not `F_3`, and the seed specifies no
field encoding, total zero-padding/index convention, small-carrier branches,
reversal or restriction law, or reconstruction theorem through adjacent
differences, the generated algebra/commutant, and a selected block. Different
choices can alter every downstream algebraic object. The idea is therefore
retained only as an underdefined global representation, not as an authorized
experiment or a sourced path to a deep split.

## Rank-three Plücker identities and the packed-caller boundary

Apel fixes the rank-three four-term Grassmann--Plücker convention, its
repeated-index specialization, alternating bracket normalization, and
repeated-label zeros. Speyer and Sturmfels state quadratic generation of the
generic Plücker ideal over the integers; at rank three this supports a complete
quadratic universe on original homogeneous vectors. Natura and
Cheung--Gleixner--Steffy supply exact rational Farkas/linear-combination
certificate semantics and independently replayable rational multipliers.

Together these sources make the proposed finite algebraic search precise in
the coordinate tier: on the 22 original packed labels, use every increasing
triple bracket and every normalized rank-three quadratic relation, with no
constructed intersection labels. They do not bridge the project's unchanged
abstract packed caller into that tier. `PackedElevenElevenOpen567` and a
crossing strong `3+3` witness provide neither realizing homogeneous vectors
nor a uniform strict determinant-sign theorem for every bracket factor.
Filtering away unsigned monomials before such a sign inventory is proved
would repeat `B010-I04`'s central defect in a larger search space. A
realizability premise would also strengthen, rather than prove, the literal
`PackedBalancedThreeThreeImpossible567` terminal. The complete cone is
therefore sourced but unauthorized until an independent caller-to-sign bridge
exists.

## Tope graphs, gatedness, and gated amalgams

Knauer and Marc characterize COM tope graphs as antipodally gated partial
cubes and specialize the result to oriented matroids. Their theta classes give
the usual hypercube-coordinate convex halfspaces, and antipodal gated
subgraphs correspond to covectors. This retains substantially more sign
compatibility than a single pivot tournament or an equality class in a
maximally refined pair coloring.

That machinery does not provide the decomposition used by
`FD011-TOPE-GATED`. Gatedness of one antipodal subgraph says every exterior
vertex has a unique metric gate; it does not create a second gated side, their
overlap, a union equality, or properness. Chepoi--Knauer--Marc give successive
gated-amalgam construction for hypercellular partial cubes, a strictly
narrower class, and no sourced theorem or project producer makes the relevant
rank-three tope graphs hypercellular. A canonical minimum-boundary amalgam and
its theta-label-to-point-cut map therefore remain undefined rather than
source consequences.

## Complete covectors and binary-matroid connectivity

Knauer and Marc's covector account is stronger than the tope-only summary: it
fixes the signed covector set, zero and opposite covectors, reorientation and
deletion, the topes, and reconstruction from the associated antipodal gated
subgraphs. Oxley's standard representation of a binary vector matroid and its
connectivity function make a binary incidence matrix and a proposed minimum
connectivity shore unambiguous once the matrix and ground set are fixed.
Oum's cut-rank convention independently confirms the familiar rank over the
binary field for a cross-shore adjacency submatrix; it does not prove that the
project's covector incidence construction has a useful cut.

These sources do not complete `R012-COVECTOR-PAIR-CONNECTIVITY`. The proposed
instruction to “recursively choose the least proper minimum” is not a total
mathematical object: a shore and its complement tie, no complement
normalization or secondary key is specified, empty and small carriers lack a
branch, and recursion could either recompute covectors after oriented-matroid
deletion or merely restrict the original binary column matroid. Child order
and terminal conventions are also absent. Consequently no sourced theorem yet
connects a canonical covector cut to a recursive point decomposition or the
load-bearing consumer.

## Strict gammoids versus owner-linked Pascal demands

Mason, Ingleton--Piff, Perfect, and the explicit modern definitions of
Afzali--Law--Müller source the standard finite picture: in a directed graph
with fixed exits, sets linkable to those exits by mutually vertex-disjoint
directed paths form a matroid; a strict gammoid's ground set is the whole
vertex set. These theorems are exact once the digraph and exits are supplied.

They do not define the proposed owner-interleaving object. The Batch012 seed
does not specify its prefix vertices or state `q`, edges and sign acceptance,
demand sources, exits, acyclicity, or a function assigning a newly closed
crossing to a `LeafOwner`. The compiled `leafOwner_nonreuse` theorem is only
injectivity for leaf owners already present in a supplied decomposition tree.
Moreover, restricting a strict gammoid to demand-source vertices must be
stated explicitly; it is not the same definition as taking all DAG vertices.

The numerical return is independently missing. The existing TransitionHall
consumer assumes Hall expansion for finite sets of raw frontier spans and
bounds their raw cardinality. A low gammoid rank merely makes several demand
sources dependent; it does not reduce their number or imply the ambient
`left.card + right.card <= 21` obligation in `PascalTailTwoSideBound 5 6 7`.
Thus standard gammoid theory is source-grounded, while both the project graph
and its Pascal consumer remain new mechanisms.

## Orchard deletion partitions and radial selectors

Bacher's Orchard morphism and the planar treatment with Garber source a
natural unordered partition of a generic configuration into at most two
classes using separating-hyperplane parity. Applied after deleting one point,
the relation lives on the surviving labels; the restriction vector records
zero at the deleted anchor. The sources do not choose a shore for that anchor,
turn all deletion partitions into total cuts of the original label set, or
connect a radial-score maximum to predecessor-hyperedge bicoloring.

That distinction blocks the proposed Orchard-pencil selector before any
fixture test. Separately, no primary source was authenticated for the proposed
all-lag `delta * (m-delta)` radial-necklace kernel or for a theorem converting
its balanced maxima into hard predecessor-edge coverage. Both ideas therefore
remain project inventions requiring prospective definitions and a structural
coverage observation, rather than sourced consequences of Orchard theory.

## Lexicographic extensions versus recursive point decomposition

Hochstättler and Wilhelmi give the standard cocircuit-localization description
of a one-element extension and define signed lexicographic extensions by the
first nonzero coordinate in an ordered signed support. They also record
reorientation to a positive lexicographic extension and prove preservation of
Euclideaness; their main shelling results concern topological sweeps and the
tope-cell poset of a Euclidean oriented-matroid program.

Those results do not establish the structural bridge proposed by
`RC010-LEXEXT-PEEL`. In particular, they do not bound the minimum
lexicographic-support depth of an arbitrary deletion localization, prescribe a
canonical sequence of minimum-depth deletions, align that sequence with a
registered point-set root, or imply `HasDeepBelowSplit` or `D-DECOMP`.
Vertex-shellability and recursive atom orderings in the sourced tope-cell
poset must therefore remain distinct from the project's recursive deep-below
decomposition until an explicit theorem connects them.

## Existing formal proof assets

- **Isabelle/HOL, exact cases through six:** Marić's 2019 paper formalizes a
  SAT-based proof of the conjecture for `n ≤ 6`. It validates the finite
  orientation/SAT approach but is not a Lean artifact.  The official ARGO
  `HappyEnding.zip` was retrieved and hash-audited on 2026-08-15.  Its three
  files contain checked cases only through five and dormant formula-generation
  code for `6/17`, with no license, session root, generated formula, proof, or
  final theorem.  A complete licensed distribution or a separately reviewed
  independent finite proof is required before this route can resume.
- **Lean 4, Erdős--Tuza--Valtr `(n,4,n)`:** Baek's Apache-2.0 repository states
  its main theorem as `theorem main` and includes a cup--cap theorem. Its
  configuration API is the leading reuse candidate, subject to revision and
  toolchain audit.
- **Lean, empty hexagon number:** Subercaseaux et al. formally verify the
  `h(6)=30` SAT pipeline. The theorem is out of scope, but its connection of
  point geometry to propositional assignments and certificate checking is a
  relevant engineering model.

No checked source found in this initial search claims a Lean proof of the full
exact formula, and such a claim would contradict the current literature status.

## Consequences for this project

1. The canonical theorem must state **both** forcing and sharpness. A Lean proof
   of `ForcesConvexPolygon n (2^(n-2)+1)` alone is only the difficult upper
   half; a threshold definition without a witness can hide this distinction.
2. The project should maintain a direct `ℝ²` statement even if most reasoning
   occurs in a finite ordered configuration. The bridge is part of the proof.
3. The all-`n` lower construction is the first sensible formal reproduction.
   It exercises recursive separation and convex-position lemmas needed later.
4. Reproving `n ≤ 5` in Lean provides small exact controls. Importing or
   rebuilding the `n=6` certificate is useful only if it exposes a reusable
   obstruction for `n=7`; otherwise it is not the research frontier.
5. The Erdős--Tuza--Valtr implication lattice and the decomposable-set theorem
   are the two clearest current structural footholds toward the exact formula.
6. Purely abstract ordered-hypergraph reasoning is unsafe unless every axiom
   used is proved for realizable planar orientations. Recent counterexamples
   make this a central design constraint, not a technicality.

## Proposed formal milestones

These are milestones, not claims that the route is known.

| Milestone | Mathematical status | Lean completion condition |
| --- | --- | --- |
| Direct statement layer | Definition | Exact formula is represented as forcing plus a sharpness witness over finite subsets of `ℝ²` |
| Representation bridge | Known foundations | Orientation, collinearity, convex-hull, cup/cap, and ordered-configuration predicates are connected by compiling equivalence/implication lemmas |
| All-`n` lower bound | Known theorem | A recursive `2^(n-2)` construction and proof of avoidance compile for every `n ≥ 3` |
| Exact small controls | Known theorem | `ES(3)`, `ES(4)`, and `ES(5)` compile under the same public API; `ES(6)` is separately certificate-checked if adopted |
| Decomposable sets | 2026 known theorem | The exact formula for the published decomposable class compiles, with definitions matched to the paper |
| Indecomposable obstruction | New progress target | A new compiling theorem rules out or structurally restricts a nontrivial class of minimal counterexamples |
| General upper bound | Open target | `ForcesConvexPolygon n (2^(n-2)+1)` compiles for all `n ≥ 3` |
| Exact formula | Destination | General upper bound and sharpness construction combine into `ErdosSzekeresConjecture` with no placeholders |

## Gaps in this initial survey

The Morris--Soltan survey contains 89 references through 2000. This pass has
not individually authenticated every one because many concern side variants.
A defensible claim of "everything published" would additionally require
database exports from MathSciNet, zbMATH, Scopus/Web of Science or OpenAlex,
forward-citation deduplication for the 1935 paper and the 2000 survey, and
manual classification of non-English and non-digitized sources. The living
ledger therefore records coverage and omissions instead of asserting false
exhaustiveness.
