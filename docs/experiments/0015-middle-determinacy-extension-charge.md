# Middle determinacy and the `(5,6,7)` extension charge

Date: 2026-08-04

Status: route-selection evidence plus compiling Lean infrastructure; the
two-side bound remains unproved.

## Question

The residual `TwoCapFreeSidesBound567` reduction produces either a four-cap
meeting both ordered sides or a strong six-set.  Can nonextension by each
unused vertex be converted into a small signature count, and is the abstract
22-vertex forcing statement itself true at the balanced cuts?

## Bounded review

The Sol/Fable packet at SHA-256
`d7611ab3099cfc0088afed4463db4628c3f93067ffea722002350e9bdf6f1a69`
returned `partially_supported` from both reviewers.  They agreed that the bare
one-vertex failure certificates are valid with explicit ambient-subset,
ambient-membership, and freshness hypotheses, but have no quantitative
content by themselves.

Sol recommended one bounded identical-profile collision test before pursuing
an abstract classification.  Fable recommended route-independent cap
localization, a middle-determinacy characterization of strong polygons, and a
direct balanced-cut SAT encoding before choosing between the abstract and
deep-below routes.

## Lean results

The following now compile without placeholders:

- `IsStrongPolygonSet χ s ↔ IsMiddleDeterminedOn χ s`: within a strong set,
  the color of a triple depends only on its middle vertex;
- the corresponding characterization of strong-set avoidance on every
  fixed-cardinality subset;
- generalized cap and strong-polygon one-vertex failure certificates, with
  the bad triple or quadruple proved to contain the new vertex;
- consecutive localization of a four-cap extension failure among the three
  consecutive triples of the sorted five-set;
- a five-cup bridge theorem forcing the last-pair turn through every later
  ambient vertex to be right;
- nesting of those bridge colors under the one-change law.

These are reusable formal results, not a proof of the cardinal bound 21.

## Identical-profile falsification

`scripts/check_witness_profile_collision.py` fixes either a cap or a strong
polygon and constrains two same-gap vertices to have identical colors with
every witness pair.  It then imposes the residual one-change and forbidden
configuration clauses and independently checks any SAT assignment.

Two small controls are SAT and validated:

| witness | parameters | variables | clauses | CNF SHA-256 |
| --- | --- | ---: | ---: | --- |
| crossing four-cap | `n=6`, cut `3`, witness `0,3,4,5`, pair `1,2` | 20 | 143 | `fa3993ae7d16841e6dc8aede6c6105991d74194ae915e811c7e8e5ec132d184b` |
| strong six-set | `n=8`, cut `4`, witness `0,3,4,5,6,7`, pair `1,2` | 56 | 992 | `71113c5b3e18fddcf45fa018babe054b537891dd8f3f553538eb93811ec955e1` |

Thus an unconditional two-vertex identical witness-profile collision lemma is
false.  Any successful count must retain global information among outside
vertices, not only their colors against one witness.

## Compact strong-seven encoding

`scripts/check_two_cap_free_sides_middle.py` introduces a shared XOR variable
for each pair of triples having the same middle vertex.  By the Lean
middle-determinacy theorem, one clause per seven-subset excludes a strong
seven-set by requiring at least one such pair to differ.  SAT assignments are
checked directly against the original definitions; UNSAT results remain
computational evidence because these runs did not emit a checked proof
certificate.

The two previously unresolved balanced cuts are now UNSAT:

| cut | variables | clauses | strong blockers | seconds | CNF SHA-256 |
| ---: | ---: | ---: | ---: | ---: | --- |
| 10 | 42,068 | 492,828 | 170,544 | 277.550 | `f934ed95abb1e96f301708715b701f0de735a2935eced7f2813298e882453e28` |
| 11 | 42,068 | 492,783 | 170,544 | 289.393 | `7c5b2001dfddc99e6892fb6bd5dc4b506db017049a1d375d5a016e64009c0292` |

Together with the earlier cut results, this is computational evidence for the
entire 22-vertex abstract forcing statement.  It does not promote that
statement to a theorem.

## Disposition

Retain the abstract `TwoCapFreeSidesBound567` route: the balanced computation
found no counterexample, and middle determinacy exposes substantially more
structure than arbitrary strong-failure certificates.  Do not pursue a
witness-only profile pigeonhole argument.  The next proof item is a genuine
global collision/counting lemma combining:

1. the forced bridge colors from a five-cup on the large side;
2. consecutive cap-failure locations;
3. middle-color disagreement forced on every seven-subset; and
4. triples among the vertices outside the selected witness.

The `HasDeepBelowSplit` refinement remains the fallback if that global count
cannot be closed abstractly.
