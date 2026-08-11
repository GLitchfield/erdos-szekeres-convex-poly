# Experiment 0100: diagonal `k = 9` extreme exchange

Date: 2026-08-11

Status: Both normalized contracts independently certified computationally;
partial Lean certificate/semantic layers compile, final theorem pending

## Question

The monolithic double-deletion gluing proposal is circular: under the proved
diagonal theorem at `k`, it is equivalent to assuming the next diagonal
theorem.  A noncircular repair keeps only the extreme step needed by the
elementary gluing lemma.

On 17 ordered vertices, take an eight-point cup block and an adjacent
nine-point cup block.  Remove the far endpoint `q` of the nine-block, leaving
an eight-point core.  Assuming the one-change law, no four-cap, and no strong
ten-set, must some point `p` of the small block make `insert p core` a
nine-cup?  The reversed orientation is tested separately.

No ambient ten-cup avoidance is assumed or encoded.

## Compiling elementary consumer

`StructuralChargingPascalCupBlocks.lean` proves

```lean
isCupSet_insert_two_of_extreme_cup_extensions
```

If `insert x core` and `insert y core` are cups, `x` lies left of every core
vertex, `y` lies right of every core vertex, the core has at least two
vertices, and the ambient coloring satisfies the one-change law, then
`insert x (insert y core)` is a cup.  This theorem is certificate-free and
compiles.  It converts the proposed extraction theorem into the needed larger
cup without restating that cup in the extraction premise.

## Exact bounded audit

Both normalized abstract-signotope searches are UNSAT.  The encoding has
5,440 variables and 60,056 clauses before dependency trimming.  It uses
auxiliary equality variables for the exact strong-set law, avoiding the much
larger explicit strong-pattern expansion.

| Orientation | Dense variables | Core clauses | LRAT additions |
| --- | ---: | ---: | ---: |
| `8+9` | 1,811 | 2,141 | 1,347 |
| `9+8` | 1,318 | 1,450 | 920 |

An independent checker reconstructs all 60,056 semantic clauses without
importing the producer, matches the original-clause dependency maps, validates
the dense variable maps, replays both full and dense LRAT proofs, derives the
empty clause, and rejects corrupted clause-map and final-hint controls.

Dense certificate hashes:

- `8+9` CNF:
  `d9d6ed10abe6c079a090a0bc77af4533c5836f9c4ea75e847e62133694688856`;
- `8+9` LRAT:
  `528443c8674348d9cc72154d855d4632b8482104559a0c1186ea8feae125f6cc`;
- `9+8` CNF:
  `29d3c1eca4838077f6f5ca2b20c1ba4d0662fdb28804f8de0f2a0048c3b9dc75`;
- `9+8` LRAT:
  `b7960e8676216575de8bde9a1e68eeaeac3a257fc475e11039008831b8ffc929`.

The independent checker result has SHA-256
`8519d3f8464f15398905689258f38d570c7cf77c44fb85b8e6f3973d820c15dc`.

## Evidence boundary and next gate

This is still computational evidence rather than the requested theorem. Both
bare dense LRAT modules now compile, as do the lightweight encoding boundary,
both named-atom modules, and three semantic chunks. The completed imports peak
below 2.2 GiB and use only the project's standard axiom boundary.

The frozen normalized orientation theorems and conjunction remain generated
but uncompiled. Seven retained no-strong-ten clauses each reduce to an isolated
420-conjunct helper; several bounded monolithic, spanning-tree, and clause-local
elaboration attempts were stopped without a Lean error before exceeding the
resource limits. Their status is therefore an engineering/formalization
blocker, not a refutation. The current exact completion gate is to decompose
those seven helpers into compiling proof terms, finish every semantic chunk,
and only then compose the two LRAT contradictions with the repository
predicates. No ambient ten-cup avoidance has been introduced.

The canonical partial-promotion result has SHA-256
`4763c713d7dd74a94c036682646f1322429825140cbfb700f812e5cb0395006d`.
Only after the normalized declarations compile may this experiment be marked
complete or used as a proved E3 successor ingredient.

Two further bounded elaboration architectures were tested on the smallest
retained `9+8` no-strong-ten clause. The first replaced the full 420-way
destructuring by 112 typed projections through the midpoint-balanced
conjunction tree; every projection has depth eight or nine. The second shared
the tree at depth four before taking local projections. Deterministic tests
verified all 420 projection paths and the same 112 selected negative atoms in
all seven clauses, and all certificate hashes remained unchanged.

Both warm single-job Lean builds used a full CPU core and remained near a few
GiB of memory, but each reached the ten-minute gate without a diagnostic.
This stops direct and depth-four projection extraction as the current repair.
It does not refute the extraction theorem. The next engineering gate must
split the 120 derived middle-color facts and final finite-case argument into
smaller modules, with the same frozen clause and certificate. No generated
uncompiled theorem module is retained as completed work. The canonical
projection-attempt result has SHA-256
`5b34b3137e2cff60e98c458b83915e0c7f2c48b56658899743366003393ec585`.

Ignored audit artifacts are under
`runs/agents/20260811-wave3/extreme-exchange/`.
