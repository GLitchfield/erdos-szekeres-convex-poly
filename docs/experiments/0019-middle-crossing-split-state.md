# Middle crossing strong-six state

Date: 2026-08-05

## Question

Can a `3+3` crossing strong six be replaced by an extreme `1+5` or `5+1`
witness, or do two disjoint `3+3` witnesses already force a cap five, cup six,
or strong seven?

The bounded review packet has SHA-256
`3b1bc9f5737ee6c33e3566dce112466e2c1da93be961a0d13339a668e44ef53d`.
Both reviewers rejected the deletion-preserving replacement argument because
packing controls only one deleted six-set at a time. They recommended retaining
the disjoint partner and its mutual middle-extension failures. The review is
advisory and does not certify a theorem.

## Compiling Lean results

`StructuralChargingMiddleSplits.lean` proves the following without `sorry`,
an external oracle, or a new axiom.

1. In a strong six, any three right-colored internal middle positions form a
   cap five together with the two polygon endpoints.
2. Four left-colored internal positions make the whole strong six a cup.
3. Consequently a strong six avoiding cap five and cup six has exactly one or
   two right middle positions. This requires no one-change hypothesis beyond
   the already assumed strong-polygon law.
4. Deleting any packed strong six produces a disjoint strong-six partner. In
   the no-strong-seven branch the pair is mutually middle-obstructed: each of
   the twelve directed single-vertex extensions fails middle determinacy.
5. If neither side contains an internal strong six, the same partner has one
   of the five proper crossing splits. Under ambient `(5,6)` avoidance, both
   polygons have weight-one-or-two middle words.
6. Every one of the twelve directed failures has a side-aware three-state
   normalization. For a left-side probe the left-endpoint and middle roles
   remain interleaving cases, while a right-endpoint failure has both earlier
   endpoints and the shared middle in the left side. The right-side statement
   is the order-dual: a left-endpoint failure has its shared middle and both
   later endpoints in the right side.

The general split classifier was extracted from the earlier packing theorem
so it applies to the particular mutually obstructed partner rather than to a
second uncontrolled existential witness.

## Checked falsification

`scripts/check_middle_split_pair.py` fixes two disjoint strong sixes

```
(0,1,2,6,7,8) and (3,4,5,9,10,11)
```

across an ordered `6+6` cut. It imposes one-change, side cap-four avoidance,
and ambient avoidance of cap five, cup six, and strong seven. CaDiCaL found a
SAT assignment in 0.222 seconds. The CNF SHA-256 is
`50bd35fa57ab61c832e200873b37dc87fd972393afef313899cf09b940c16125`;
the model SHA-256 is
`cb70f3fe369baee0872d43ec39bd1d73d0d27d0c3ab7308124c7f5bba3c0e2c1`.

`scripts/verify_middle_split_pair_model.py` imports no generator and checks all
220 triple assignments directly. It validates the model and reports middle
words `LLRR` and `LRLL`, realizing weights two and one respectively. Thus two
local `3+3` witnesses do not force a target outcome. This checked model is a
refutation aid, not a Lean proof of a positive result.

## Next theorem

This target is continued in [experiment 0020](0020-middle-failure-classes.md)
and [experiment 0021](0021-middle-bridge-certificates.md). The localized cores
now refine to indexed anomaly/fan classes and then to a common bridge
certificate. The strongest surviving bare two-probe compatibility statement
is proved in Lean; stronger gluing conclusions were exhaustively refuted.
