# Adjusted-promotion capacity counterexample

## Question and bounded gate

Experiment 0052 found no failure through support size eight and selected
adjusted Hall as the next theorem contract. Before attempting that proof, the
first unenumerated alternating root was tested at `k = 7`, support size ten.
The gate was bounded to an explicit pair of five-vertex reverse-comb children,
eight cores, 16 GiB RAM, 30 minutes, and 5 GiB output. Success meant either a
fixed-rank adjusted-capacity obstruction or survival of that context.

The two children have supports `0x155` and `0x2aa`; their alternating root has
coloring `0xcde50debf387c0debf57f9c3e07f00`. A compact producer reconstructs
the explicit decomposition tree and computes ranks using subset witnesses.
The independent checker imports no producer code, uses the separate row-height
rank implementation, reconstructs the tree recursively, and obtains promoted
gaps directly from consecutive child vertices. The committed manifest SHA-256
is `6dd4f3c4a481220c877bf30855e4671d0fc321a853b5a1e9416d224cd42f14ad`.

## Result

The context is open: it has no strong seven-set. Its cap/rank-three adjusted
demand consists of seven crossing-frontier spans

    (0,3), (1,4), (2,5), (3,6), (4,7), (5,8), (6,9)

and four promoted hidden lower gaps

    (0,2), (2,4), (4,6), (6,8).

All eleven spans have exact ambient rank three. Therefore

    11 > choose(5, 2) = 10.

The proposed fixed-color, fixed-rank adjusted Pascal capacity is false, and
so are adjusted Hall and every injection of this additive carrier into the
unchanged ten-slot rank-three layer.

The nearby raw aggregation repair also fails on the same certificate. Across
both colors and all ranks, the adjusted group sizes are

| Group | Cardinality |
| --- | ---: |
| cap, rank 2 | 5 |
| cap, rank 3 | 11 |
| cup, rank 2 | 5 |
| cup, rank 3 | 11 |
| cup, rank 4 | 3 |
| cup, rank 5 | 1 |
| **total** | **36** |

The single untagged nonempty Pascal window has only
`sum_{r=2}^6 choose(5,r-1) = 31` slots. Giving each color a separate 31-slot
window would pass this witness but double the resource and therefore does not
preserve the target `2^(k-2)` exponent.

## Lean result

`StructuralChargingAdjustedCounterexample.lean` kernel-checks the explicit
tree, deep-below root split, recursive decomposability, and absence of a strong
seven-set. It proves exact rank three for all eleven spans and then proves:

- `adjusted_rank_three_demand_exceeds_pascal`;
- `not_adjusted_rank_three_endpointRankTransitionHall`; and
- `no_adjusted_rank_three_slotting`.

These results use no `sorry`, `admit`, unsafe axiom, or external oracle. The
Python certificate is reproducibility support; the mathematical refutation is
the compiling Lean theorem.

## Review and disposition

The bounded review packet SHA-256 was
`dbda4bbe1a4f89dadcdd587631a02f3c5deec9bf077821df8d9c4917b6f668a9`.
Sol returned `partially_supported` with medium confidence. It verified that
the genealogy survives, that the adjusted Hall contract is decisively false,
and that a sound proof-reuse quotient has not yet been defined. It recommended
testing a two-color, all-rank aggregate; the untagged 36-versus-31 calculation
above immediately refutes the raw additive version. Fable returned zero tokens
with a provider usage-limit error, so no Fable judgment or consensus is
claimed.

The hidden-gap genealogy remains useful: hidden sources still correspond to
noninitial parent crossings and still create genuine higher-rank spans. What
is retired is counting every old crossing-frontier request and every promoted
source as an independent fixed-rank obligation, as well as summing all such
obligations into one untagged window.

## Exclusive-choice follow-up

The innovation review proposed one exact next gate: merge every hidden source
with its complementary-color residual transition into one charge having two
alternative candidate families; merge the two initial-transition obligations
and allow the empty sentinel slot; keep all existing higher-rank crossing
obligations. This reduces the raw 36 obligations to 27 charges in the single
32-element Boolean carrier.

That precise endpoint-candidate graph is still Hall deficient. Independent
cell-mask/boundary-slot and row-height/boundary-step implementations agree:

| Quantity | Count |
| --- | ---: |
| Exclusive-choice charges | 27 |
| Maximum matching | 20 |
| Demands in compact Hall witness | 20 |
| Neighbor slots of that witness | 13 |

The witness contains six of the eight exclusive hidden-source charges and all
fourteen cap/cup rank-three crossing charges. Thus merging promotions with
rank-two residuals is not enough: the two colors' higher-rank crossing
obligations still compete independently for largely the same slots. This
falsifies the innovation proposal under the current endpoint-candidate
semantics; it does not prove that a sound cross-color proof-reuse quotient is
impossible.

No replacement main route is selected. The next strategic action is a bounded
review comparing a combined containment-minimal frontier, cross-color
proof-reuse on common endpoint spans, and a genuinely conserved tree-global
charge. Any candidate must first explain semantically why one obligation pays
another, then pass this `20 > 13` Hall witness before Lean implementation.

## Reproduction

    python3 scripts/produce_adjusted_promotion_counterexample_k7_n10.py \
      --output data/derived/e3-adjusted-promotion-counterexample-k7-n10.json
    python3 scripts/check_adjusted_promotion_counterexample_k7_n10.py \
      data/derived/e3-adjusted-promotion-counterexample-k7-n10.json
