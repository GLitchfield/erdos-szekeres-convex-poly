# Consecutive-block two-step augmentation gate

## Question

The reflected Hall reduction needs every consecutive frontier block, whereas
experiment 0039 checked only each complete frozen frontier group.  Does every
injective one-hole state on every nonempty consecutive subblock either fill
directly or admit the same length-two ownership augmentation?

The block restriction changes only the participating spans.  Their reflected
candidate families are unchanged.  For each local state, a two-step exit is
an occupied hole candidate whose unique local owner has a candidate unused by
the original local partial representative system.

## Frozen result

The gate passes.  There are 62 nonempty consecutive blocks across the four
groups and 134,236 one-hole states across those blocks.  Exactly 128,259 fill
directly; all 5,977 blocked states have a two-step exit.

| Group | Blocks | States | Blocked | Result |
| --- | ---: | ---: | ---: | --- |
| cap, rank 3 | 21 | 7,512 | 2,054 | pass |
| cap, rank 4 | 3 | 14 | 0 | pass |
| cup, rank 3 | 28 | 123,716 | 3,923 | pass |
| cup, rank 4 | 10 | 2,994 | 0 | pass |

The producer reconstructs cell-mask ideals and the replay reconstructs
row-height ideals.  They independently enumerate the blocks, one-hole states,
direct exits, augmenting exits, and completed injections.  The manifest
SHA-256 is
`faab58732a372f1d23f27c733d63f6c2d840a0b0f92cbdca0295991ab91b1043`.

## Interpretation and stop rule

This removes the smallest bounded coverage objection to the two-step route and
supports asking for a structural proof of

    state.CanFill ∨ state.HasTwoStepAugmentingExit

on a genuine arbitrary reflected consecutive block.  It remains finite
computational evidence at one frozen root, not a proof of that sentence.  A
bounded Sol/Fable review must assess the proposed promotion before the
Wayfinder selects it.  If the structural argument needs the desired Hall
inequality, an existing full matching, or exhaustive state enumeration, the
route is circular and must be rejected.

## Reproduction

    python3 scripts/check_consecutive_block_two_step_augmentation.py \
      --output data/derived/e3-consecutive-block-two-step-augmentation-frozen-n12-k7.json
    python3 scripts/replay_consecutive_block_two_step_augmentation.py \
      data/derived/e3-consecutive-block-two-step-augmentation-frozen-n12-k7.json
