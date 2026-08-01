# Initial literature review: the exact Erdős--Szekeres formula

Last updated: 2026-08-01. This is a research synthesis, not a claim of
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
Kleitman--Pachter obtained a further linear subtraction, and Tóth--Valtr cut
the leading binomial expression by about a factor of two. Vlachos,
Norin--Yuditsky, and Mojarrad--Vlachos improved constants further. These papers
develop useful notions of convexity witnesses and forbidden subconfigurations,
but none changed the exponential base.

Suk's 2017 JAMS paper introduced the decisive positive-fraction/partition
method, obtaining `2^(n+O(n^(2/3) log n))`. Holmsen--Mojarrad--Pach--Tardos
sharpened this to `2^(n+O(sqrt(n log n)))` and extended the method to
pseudoline arrangements and convex bodies. The exact formula likely needs a
structural ingredient not visible after the losses inherent in these density
and partition estimates.

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

The `ES(6)=17` computation has an Isabelle/HOL formal proof by Filip Marić.
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

The first correction layer now compiles.  Lean proves the published
Pascal-window absorption in its valid interior range and proves the missing
arbitrary-split geometry: a crossing strong polygon has exactly a cup on its
lower side and a cap on its upper side, while a crossing cup (respectively,
cap) uses at most two upper (respectively, lower) sweep endpoints.  These
vertices are proved pointwise to be actual extremes of the full chain.  These
lemmas show why the scalar threshold induction loses information at the
boundary and identify endpoint-aware chain profiles as the next invariant.

## Existing formal proof assets

- **Isabelle/HOL, exact cases through six:** Marić's 2019 paper formalizes a
  SAT-based proof of the conjecture for `n ≤ 6`. It validates the finite
  orientation/SAT approach but is not a Lean artifact.
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
