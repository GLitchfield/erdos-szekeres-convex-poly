# Allocated span Pascal-demand gate

## Question

The rooted-interface review redirected the project from finite transition
states to structural counting. Its first local question is whether exact
endpoint spans, allocated at their unique lowest separating decomposition-tree
node, have a two-sided frontier small enough to fit the adjacent Pascal
coefficient

    choose(k - 2, rank - 1).

This experiment tests that statement at the first committed boundary
k = 6, for every recursively deep-below coloring on every labeled support
of at most eight vertices and every compatible root split. It is a bounded
falsification gate, not a proof of the all-parameter statement.

## Frozen conventions

- Bit one is a cup/left triple; bit zero is a cap/right triple.
- A local span rank is the maximum cardinality of a monochromatic chain
  contained in the current node support with the stated ordered endpoints.
- Contexts already containing a strong six-set are terminal and do not
  contribute open frontier groups.
- A pair crosses the current node when exactly one endpoint is in each child.
  In a complete decomposition tree, this is precisely the pair's lowest
  separating node.
- For one color and one exact rank, interval [a,b] is dominated when a
  distinct candidate interval [c,d] satisfies a <= c and d <= b.
  The retained frontier consists of the inclusion-minimal candidate intervals.
- Its capacity is row four of Pascal's triangle:
  choose(4, rank - 1).

The gate checks a local slot count. It does not yet construct a global
injection from these slots into one outer binomial window.

The same exhaustive pass also tests the first natural construction of those
slots: project every retained span to its left endpoints, or to its right
endpoints, and ask whether the projected coloring itself supplies the required
rank chain. This is a falsification test for that construction, not part of
the capacity conjecture.

## Exhaustive result

The producer enumerated 376,764 compatible root contexts:

| context class | count |
| --- | ---: |
| open | 267,898 |
| terminal strong-six | 108,866 |
| exact-rank frontier groups checked | 631,474 |

No frontier exceeded its adjacent Pascal capacity.

| color/rank | groups | maximum frontier | capacity | minimum slack |
| --- | ---: | ---: | ---: | ---: |
| cap 3 | 156,927 | 5 | 6 | 1 |
| cup 3 | 156,927 | 5 | 6 | 1 |
| cap 4 | 121,408 | 3 | 4 | 1 |
| cup 4 | 121,408 | 3 | 4 | 1 |
| cap 5 | 37,402 | 1 | 1 | 0 |
| cup 5 | 37,402 | 1 | 1 | 0 |

Thus rank five is genuinely sharp in the tested range. Ranks three and four
retain one slot of slack through eight vertices. This does not justify
strengthening the conjectured bound by one: the slack may disappear at larger
supports.

## Endpoint-projection shortcut is refuted

The capacity observation survives, but neither raw endpoint projection proves
it. Across both colors, the left projection and the right projection each fail
in 1,208 group instances. Of the rank-three groups, 996 fail both projections.
For example, the first cup/rank-three counterexample has support mask `7f`,
lower-child mask `56`, coloring `c10040a183df`, and frontier

    [(0,2), (1,3), (2,5), (3,6)].

Neither `[0,1,2,3]` nor `[2,3,5,6]` contains the projected monochromatic
chain that the shortcut requires. The color-dual cap counterexample is stored
in the manifest. Consequently, the next proof must use the exact child-ray
incidence of a crossing span; ordinary left- or right-endpoint cup--cap
projection loses essential information.

## Independent replay

The producer and checker share only the manifest contract.

- The producer uses the existing bottom-up decomposable-coloring engine,
  direct subset masks for exact chain ranks, math.comb, and explicit
  pairwise domination.
- The checker imports no producer code. It rebuilds colorings through a
  recursive cache, enumerates middle-vertex subsets directly, computes
  capacities from a Pascal table, and finds the frontier by a
  descending-left skyline scan.

The checker reproduced the support-size counts, rank census, saturation
examples, absence of a capacity violation, both projection-failure censuses,
their first witnesses, and canonical context digest

    056ad8113dff790c5dba41779f51d5dc944d9bc46996b2acf1b4b7b2e60c46ee

## Lean promotion

StructuralChargingPascalDemand.lean supplies two formal components:

1. publishedSpanPascalDemand k rank = choose (k - 2) (rank - 1) and
   sorry-free uniform bounds for both one-step published threshold jumps;
2. LowestSeparatedSpanAllocation, with a compiling existence-and-uniqueness
   theorem for distinct retained endpoints and a theorem that their allocated
   node places them in opposite children.

StructuralChargingSpanFrontier.lean now adds completed, compiling definitions
and lemmas for exact endpoint-span ranks, allocated inclusion-minimal
frontiers, and all four exact parent-rank/child-ray-rank equivalences. Under a
no-strong-`k` hypothesis it proves that a span has rank below `k`, proves the
opposite cup/cap ranks at the same crossing pair sum to at most `k + 1`, and
proves that frontier endpoints are injective and occur in the same order.

The file also freezes `AllocatedExactRankSlotting`, an explicit injection of
the frontier into the `(rank - 1)`-subsets of `Fin (k - 2)`, and proves

    allocatedExactRankFrontier_card_le_spanPascalDemand_of_slotting

from any such slotting. These are completed Lean reductions, but the slotting
construction itself and therefore the unconditional frontier-capacity
inequality remain open. The next Lean target is to construct that slotting from
the child-ray normal forms and complementary-rank constraint. Only after the
local construction is complete may the project attempt the global injection
into `decomposableBinomialWindow`.

## Reproduction

    python3 scripts/enumerate_allocated_span_pascal_demand.py \
      --maximum-n 8 --strong-size 6 \
      --output data/derived/e3-allocated-span-pascal-demand-k6-n8.json
    python3 scripts/check_allocated_span_pascal_demand.py \
      data/derived/e3-allocated-span-pascal-demand-k6-n8.json
