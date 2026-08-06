# Two-step ownership-augmentation gate

## Question

Experiment 0038 refuted the fixed boundary-priority walk because an occupied
ideal can be stolen straight back.  Is the cycle itself superficial?  More
precisely, for every blocked one-hole state of each frozen frontier group, can
the hole take some occupied candidate whose unique owner has a candidate not
used by the original partial representative system?

Such a witness is a length-two augmenting path.  Transfer the selected hole
candidate from its owner, then put the owner's fresh candidate into the new
hole.  This is weaker than requiring the owner to have at least as many
candidates as the whole block and makes no deterministic-priority or
well-founded-descent claim.

## Frozen result

The cell-mask producer and independent row-height replay agree on all 85,920
one-hole states in the four frozen `n = 12`, `k = 7` groups.  Of these, 81,032
fill directly and 4,888 are blocked.  Every blocked state has a two-step exit.

| Group | States | Direct | Blocked | Exit-count histogram on blocked states |
| --- | ---: | ---: | ---: | --- |
| cap, rank 3 | 5,208 | 3,612 | 1,596 | `1: 1,596` |
| cap, rank 4 | 12 | 12 | 0 | empty |
| cup, rank 3 | 78,236 | 74,944 | 3,292 | `2: 68`, `3: 3,084`, `5: 140` |
| cup, rank 4 | 2,464 | 2,464 | 0 | empty |

The manifest SHA-256 is
`2f3f36bf1ff3ec4e1ac613b2a3fcf87f0d4831d5f6540268a8d12637bfc14ac5`.

Lean now defines `FiniteCandidateHoleState.HasTwoStepAugmentingExit` and
proves that this explicit certificate yields a full system of distinct
representatives and therefore the block Hall inequality.  The proof performs
the two updates directly; it assumes neither Hall nor an already completed
matching.

## Claim boundary

The census is bounded computational evidence.  The Lean theorem proves only
the generic implication from a supplied two-step certificate.  Neither
artifact proves that arbitrary reflected frontier blocks have the certificate,
nor does it establish the global outer-window injection or the exact
Erdős--Szekeres formula.  Experiment 0040 tests the immediate coverage concern:
all consecutive subblocks of the same frozen groups.

## Reproduction

    python3 scripts/check_two_step_ownership_augmentation.py \
      --output data/derived/e3-two-step-ownership-augmentation-frozen-n12-k7.json
    python3 scripts/replay_two_step_ownership_augmentation.py \
      data/derived/e3-two-step-ownership-augmentation-frozen-n12-k7.json
