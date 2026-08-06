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
examples, absence of a violation, and canonical context digest

    056ad8113dff790c5dba41779f51d5dc944d9bc46996b2acf1b4b7b2e60c46ee

## Lean promotion

StructuralChargingPascalDemand.lean now supplies two formal components:

1. publishedSpanPascalDemand k rank = choose (k - 2) (rank - 1) and
   sorry-free uniform bounds for both one-step published threshold jumps;
2. LowestSeparatedSpanAllocation, with a compiling existence-and-uniqueness
   theorem for distinct retained endpoints and a theorem that their allocated
   node places them in opposite children.

These are completed Lean results. The observed frontier-capacity inequality
remains computational evidence. The next Lean target is the general local
theorem

    allocatedExactRankFrontier_card_le_spanPascalDemand

under an explicit no-strong-k hypothesis. Only after that theorem is proved
may the project attempt the global injection of local slots into
decomposableBinomialWindow.

## Reproduction

    python3 scripts/enumerate_allocated_span_pascal_demand.py \
      --maximum-n 8 --strong-size 6 \
      --output data/derived/e3-allocated-span-pascal-demand-k6-n8.json
    python3 scripts/check_allocated_span_pascal_demand.py \
      data/derived/e3-allocated-span-pascal-demand-k6-n8.json
