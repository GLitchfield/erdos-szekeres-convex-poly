# Singleton-context residual oracle

Date: 2026-08-05

## Question and evidence boundary

After the local bridge, packing, and realizability repairs were retired, the
pre-vetted fallback was to design a new E3 invariant and test it against every
available transition collision before promoting it to Lean. This experiment
constructs a complete reference oracle at the first `k = 6` boundary:

> Which eight-vertex recursively decomposable colorings are distinguishable
> by their own anchored cup/cap profile or by placing them in any one-vertex
> deep-below root context?

This is exact bounded computation, independently replayed. It is not a
uniform invariant, a counting theorem, or a Lean proof of a new mathematical
result. In particular, the full residual truth table is an oracle for finding
a smaller state, not a candidate state to formalize verbatim.

## Property-relative observation

For `k = 6`, an open coloring is observed by its complete sweep-gap word. At
each gap the word records the clipped maximum cup and cap lengths in the three
relations `anchorLeft`, `anchorRight`, and `straddled`. A coloring containing
a strong six-set is collapsed to one terminal symbol, because such a branch
has already met the target.

For each of the 186,888 recursively decomposable colorings on eight ordered
vertices, the producer evaluates:

- its own observation; and
- all 18 singleton extensions: each of nine insertion positions, with the
  child serving as either the lower or the upper root part.

Two colorings have the same one-step residual state exactly when all 19
property-relative observations agree. The two extreme insertion positions
and both root orientations are included; no symmetry reduction is assumed.

## Producer and independent replay

`scripts/enumerate_singleton_residuals.py` uses a bottom-up enumeration of
child colorings, byte-table order embeddings, and pair-mask tests for strong
sets. It writes the 18 large context tables under ignored `runs/` and commits
only a compact manifest.

`scripts/check_singleton_residuals.py` imports no producer code. It uses a
memoized recursive coloring enumeration, embeds each triple directly, checks
strongness by explicit bit equality, and recomputes every profile, residual
class, regression, and digest. A small `5 -> 6` unit control also compares the
two implementations on every record.

On the full run, the producer took 55.67 seconds and 367 MiB peak RSS with
eight workers. The checker took 114.38 seconds and 524 MiB peak RSS. Both were
well inside the declared 30-minute, 16-GiB, 5-GiB limits. The ignored context
tables occupy 132 MiB.

## Exact result

The independent replay agrees on:

| Quantity | Count |
| --- | ---: |
| Decomposable eight-vertex colorings | 186,888 |
| Immediate property-relative observations | 5,917 |
| One-step singleton residual classes | 7,159 |
| Nontrivial residual classes | 6,237 |
| Singleton residual classes | 922 |
| Largest residual class | 63,982 |

Every singleton context has 85,797 open and 101,091 terminal outputs. The
large residual class is therefore expected: already-closed child colorings
remain terminal in every extension.

The first genuine refinement has equal child observations but differs after
inserting an upper singleton at position one, equivalently making the child
the lower root part. At parent gap six, one coloring has a straddling cup of
length five while the other has maximum four. Thus the new information is an
interior extension capability, not a changed child maximum.

The committed all-gap collision is separated in the same context. Its parent
profiles first differ at gap six in the `cup_anchor_right` coordinate, with
values four and three. This passes the mandatory regression gate.

The complete pair-rank collision is not separated: its two child observations
and all 18 parent observations agree. An exploratory one-implementation
widening checked every open continuation obtained by adding up to four
successive singleton roots. The numbers of observations at depths one through
four were `18`, `360`, `5,280`, and `50,160`; no observation differed. This
depth-four control is explicitly not part of the independently replayed exact
manifest.

## Compression diagnosis

One singleton context refines the 5,917 immediate observations to at most
6,100 classes. A deterministic greedy cover requires both root orientations
at seven interior positions to recover all 7,159 classes. The two extreme
positions add no classes, and four of the 18 contexts remain redundant after
the greedy pass.

This rejects two simplistic interpretations:

1. One favored root position does not contain all missing information.
2. Refining the anchored profile alone still does not recover the complete
   predecessor correlation witnessed by the pair-rank collision.

At the same time, the residual state is far from injective. The useful new
datum is concentrated in how near-maximal chains respond to an interior
insertion. The next candidate should therefore describe **critical rooted
chain footprints**: for each near-threshold cup or cap, the interval of cuts
and root roles at which it can create a larger anchored chain. Such a state
must be expressed without retaining a word indexed by every ambient vertex.

## Stop and promotion rules

- Do not promote the 7,159-class truth table to Lean as the invariant.
- Do not claim that singleton contexts are all decomposable contexts.
- Do not add more depth to the pair-rank probe unless a proposed finite
  rooted-footprint state predicts a separating context.
- Before selecting a rooted-footprint definition, obtain bounded Sol/Fable
  review comparing its finite carrier, root transition, and prospective
  `k`-only count with the alternatives.
- Lean promotion requires a uniform semantic lemma about rooted chains or
  critical cut intervals, not a theorem that merely replays this census.

## Reproduction

```console
python3 scripts/enumerate_singleton_residuals.py \
  --child-size 8 --strong-size 6 --workers 8 \
  --run-directory runs/e3-singleton-residual-k6-n9 \
  --output data/derived/e3-singleton-residual-k6-n9.json
python3 scripts/check_singleton_residuals.py \
  data/derived/e3-singleton-residual-k6-n9.json --workers 8
```

The compact manifest SHA-256 is
`d579772e329a84ad9d090aacbf3d68dc44bf52e3ae0072146f2560951679e7cf`.

## Route review

A bounded blind review at revision `d46d563` used packet SHA-256
`4058cc55c5850b4630e70a9b413a8773bdbc0251ba00f87cbab7138e5ea7d304`.
Claude Fable 5 and Codex Sol both returned `partially_supported` at high
confidence. They independently agree that rooted-chain footprints are the
best next object to specify and falsify, but reject freezing the prose sketch
as an invariant.

The material unresolved choices are whether successful cuts are intervals,
the precise domination order, the scope of retained terminal-endpoint
incidence, and the proposed `k`-only weight. The selected work item is only a
bounded specification task: define the atoms and test critical-cut convexity,
then demand singleton observation and self-composition congruence on the
existing census. A two-vertex interleaved-root gate must follow before any
uniform route claim.

The proposed first Lean theorem is a uniform iff: a singleton deep-below root
extends a specified child cup or cap chain exactly when the local criticality
predicate at its retained endpoint, insertion cut, and root role holds. If
interval storage survives, cut-set convexity is a separate required lemma.
