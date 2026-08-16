# Initial literature review: the exact Erdős--Szekeres formula

Last updated: 2026-08-13. This is a research synthesis, not a claim of
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
What remains is not the local color geometry or branch selection: it is the
rest of the original Pór--Valtr point-set producer, followed by the
positive-fraction recurrence and asymptotic assembly.  Thus this is still not
a formalization of Suk's positive-fraction theorem or asymptotic upper bound.

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
