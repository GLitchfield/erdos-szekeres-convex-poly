# Research checkpoint

Updated: 2026-09-18 16:53 EDT

## Authoritative state

- Agent: `codex:agent-run-16139d2dbe904066`; usage window
  `window-fa0964031a4a457d`; native thread
  `01a0b63b-68ba-73c0-b0fa-93bb1f4a38b9`.
- Parent claim held:
  `ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end`.
- New-node claim held:
  `ErdosSzekeres.CtxTwoActualMarkerOppositeBoundaryCompanionNineBound`.
- Branch: `node/CtxTwoActualMarkerOppositeBoundaryCompanionNineBound`.

## Compiling result

`ErdosSzekeres.CtxTwoActualMarkerOppositeBoundaryCompanionNineBound` is
sorry-free in targeted check job `20260918-164923-515fed`.  Its exact source
is `ESBlueprint/B/CtxTwoActualMarkerOppositeBoundaryCompanionNineBound.lean`.
The theorem starts with the actual chosen-kept cut, transports the retained
child `p` to an actual level-one marker of the companion `B`, proves
`B.maximumAt 1 = 1` from `n = 1`, and transports the two actual chosen-axis
markers to levels `N+1 < M+1`.  If `p` is strictly to one side of every
companion child, it contributes one uniform truncated opposite-axis extension
unit.  The checked two-marker triangular-linear potential then has width at
most three and gives, for every fuel and at full bound, `B <= 9`.

This is stronger than the desired `B <= 11` on the exterior-marker subcase.
It permits multiple synthetic level-one positions, arbitrary kept lists,
additional source history, inactive children and independent fuel.

Targeted receipt:

- build: one module in 3 seconds;
- extracted status: closed, `sorry=False`;
- axioms: `propext`, `Classical.choice`, `Quot.sound`;
- theorem type hash: `17c012144f8a6c19`;
- statement lock matches.

Full extraction job `20260918-165113-ce3bb7` is still running under the
required 28 GiB reservation at this checkpoint.

## Remaining mathematical obstruction

The full actual companion can have level-one marker occurrences interspersed
with companion children.  The existing independent low/high rank-pair bounds
overcount precisely there; endpoint exclusion alone does not turn their sum
into eleven.  The next diagnostic records the actual recursive values of the
canonical low/high prunings in the reviewed minimal companion enumeration,
split by the level-one marker's position relative to the two chosen markers.
It has not yet run because the full extraction occupies the shared memory
budget.

## Search and failed attempts

Exact `es search` queries with no matching theorem:

- `actual level one marker maximum one companion bound eleven`
- `two actual chosen markers opposite actual marker boundary rank loss companion eleven`
- `level one opposite marker outside all companion children two marker bound`
- `two marker triangular linear rank budget one endpoint loss`
- `opposite marker between two chosen markers bound eleven`
- `alternating axis three markers bound`

Infrastructure/proof attempts:

- job `20260918-164407-c9b228` failed because the branch ref had already been
  created while the direct sandboxed HEAD update was denied;
  `20260918-164430-f3dc68` switched to that branch successfully;
- node registration at 4 GiB (`20260918-164459-1892d7`) correctly refused its
  nested 20 GiB elaboration; `20260918-164523-1653b3` succeeded at 20 GiB;
- draft checks `20260918-164808-649a7b`, `20260918-164831-5201fb`, and
  `20260918-164858-361666` exposed respectively the missing part-positivity
  import, the namespace of `le_getD_max?_of_mem`, and no further mathematical
  obstruction; draft four closed.

## Resume actions

1. Follow `20260918-165113-ce3bb7` to terminal and inspect the full extraction.
2. Run `probe_companion_group_charges.py` through `es job run`, preserving its
   JSON output, then review the script before starting another trial.
3. Capture/check the exact proof, update `verified-results.json`, and obtain a
   reviewed local commit using guarded harness/git execution.
4. Continue the internal-marker coupled estimate; do not mistake this exterior
   closure for the full `B <= 11` theorem.
