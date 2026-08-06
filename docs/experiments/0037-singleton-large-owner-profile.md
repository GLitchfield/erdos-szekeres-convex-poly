# Singleton-or-block-large owner profile gate

## Reviewed target

Experiment 0036 found that every blocked one-hole state in the frozen
cap/rank-three frontier terminates after one ownership transfer. A bounded
Sol/Fable review identified the exact reason: the candidate priority was never
used nontrivially because every blocked family was a singleton. The review
selected the following state-independent profile as the cheapest next gate.

- H1: every candidate family is a singleton or has cardinality at least the
  frontier block.
- H2: every other family containing a singleton family's ideal has
  cardinality at least the block.

Fable selected this profile theorem in its blind answer. Sol initially selected
a full 80,712-state continuation, then revised its recommendation to the same
profile-only gate after reading Fable's critique. Fable's reciprocal call hit
its provider quota, so no completed reciprocal consensus report is claimed.
The frozen evidence packet SHA-256 is
`cf5e9032ec5e4b2beacbd3fe66762732c7919786ab67769c6c14e108417e6f63`;
the Fable blind result is
`9175238c16f3d5ec5b41c2b393446237472c2648f402be00d92880f04cbb64bc`,
and Sol's revised result is
`46e27c0a47628c310781cb4424b573fc79e12e7b3d9b2f1a146ee5cd43c01af6`.
These are advisory review artifacts, not mathematical evidence.

## Lean theorem

`StructuralChargingTransitionHallHoleDescent.lean` now defines
`SingletonOrBlockLarge` and `SingletonCandidateOwnersBlockLarge`. The compiling
theorem

    FiniteCandidateHoleState.
      hasDistinctRepresentatives_of_singletonOrBlockLarge

proves that H1 and H2 make every one-hole state directly fillable or fillable
after one ownership transfer. Its cardinality corollary proves the block Hall
inequality. The proof uses no candidate priority, known matching, Hall premise,
graph distance, or multi-step measure.

## Frozen result

The complete frozen root has four reflected frontier profiles:

    cap rank 3, block 6:  [10, 7, 1, 1, 9, 10]
    cap rank 4, block 2:  [6, 6]
    cup rank 3, block 7:  [10, 9, 6, 6, 3, 6, 8]
    cup rank 4, block 4:  [10, 9, 9, 10]

H1 and H2 hold in the first, second, and fourth groups. H1 fails in the
seven-span cup/rank-three group at spans `(2,5)`, `(3,7)`, `(6,8)`, and
`(7,9)`, whose family sizes are 6, 6, 3, and 6. That group has no singleton
families, so H2 is vacuous. Thus the one-transfer theorem is valid and useful,
but its hypotheses do not explain all four frozen groups.

Cell-mask and row-height implementations independently reconstruct all four
profiles and the same failure list. The manifest SHA-256 is
`dbac5a5b2b2220da01f49fd442bb35ad7b00825e948430fc8a1c0b875124538d`.

## Claim boundary and redirect

This is a profile-only frozen-root refutation, not a refutation of reflected
Hall: all four candidate systems still have SDRs. It proves that the successful
cap/rank-three ownership mechanism was a special cardinality pattern, not a
uniform explanation. Following the reviewed stop rule, experiment 0038 tests
the unchanged deterministic ownership rule only on the failing cup/rank-three
profile.

## Reproduction

    python3 scripts/check_singleton_large_owner_profile.py \
      --output data/derived/e3-singleton-large-owner-profile-frozen-n12-k7.json
    python3 scripts/replay_singleton_large_owner_profile.py \
      data/derived/e3-singleton-large-owner-profile-frozen-n12-k7.json
