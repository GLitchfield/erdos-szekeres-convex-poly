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
computational evidence at one frozen root, not a proof of that sentence.

A zero-round blind route review used clean revision
`89277094588987ce86f5dbe2d61e5cb8aab7685c` and evidence-packet SHA-256
`2ff3e016f4c17f174aec9f3b1427a7e2d8a0ec2005562bc3a370fe7522fdcebf`.
Sol returned high-confidence `partially_supported` and selected the
disjunction as the next exact target.  It isolated the missing geometry as an
overlap-to-slack or no-closed-saturated-star principle: in a blocked state,
some owner reached through the hole family must have a candidate outside the
whole used set.  Its result SHA-256 is
`1540002485803a54b804114718aa90c35f4b53a4039f0005085132845c57a0aa`.
Fable returned no mathematical answer because the provider reported exhausted
Fable 5 quota; no Sol/Fable consensus is claimed.  If the structural argument
needs the desired Hall inequality, an existing full matching, or exhaustive
state enumeration, the route is circular and must be rejected.

## Reproduction

    python3 scripts/check_consecutive_block_two_step_augmentation.py \
      --output data/derived/e3-consecutive-block-two-step-augmentation-frozen-n12-k7.json
    python3 scripts/replay_consecutive_block_two_step_augmentation.py \
      data/derived/e3-consecutive-block-two-step-augmentation-frozen-n12-k7.json
