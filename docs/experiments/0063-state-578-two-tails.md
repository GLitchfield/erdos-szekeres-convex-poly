# Experiment 0063: the `(5,7,8)` two-tail reduction

## Question

After the unconditional `(4,8,8)` state, what remains at the next bottom-up
fixed-`k=8` state, and can the first residual tail be closed by extracting a
constant-size rooted cup-block core?

## Kernel-checked reduction

`StructuralChargingNextState578.lean` proves that the exact critical root has
42 vertices. Assuming all strict fixed-`k=8` predecessor states, published
child-index arithmetic excludes lower-child sizes `11..40`. The only remaining
oriented pairs are:

- a lower child of size at most 10 against an upper child of size at least 32;
  or
- the exact `41+1` split.

Restriction preserves decomposability, the deep split, and all three avoidance
hypotheses. Thus the first family reduces to a singleton lower child and
exactly 32 upper vertices. The two tails are not color-dual inside the
asymmetric `(5,7,8)` state.

At the singleton-lower root, splitting the upper child at the root's sweep
position makes both sides four-cap-free. The `(4,7)` cup--cap bound gives side
sizes between 11 and 21, so both sides contain a five-cup. This valid Lean
reduction suggested a centered `5+q+5` local gate.

## Refuted local gate

The centered gate is false. A dedicated CNF fixes the two five-cups, the
one-change law, and every singleton deep-split crossing color on 11 vertices.
CaDiCaL returns SAT, and `check_signotope_state_witness.py` independently
checks all structural constraints and the absence of a five-cap, seven-cup,
and strong eight-set.

More decisively,
`StructuralChargingNextState578Counterexample.lean` reconstructs the witness
as the explicit recursively decomposable tree

```text
[5, [[[[[0,1],2],3],4], [[[[[6,7],8],9],10]]]
```

and proves `not_rootedCupBlocks55Force578` in Lean. The declaration compiles
without `sorry`, `admit`, custom axioms, or an external oracle; its axiom set is
only `propext`, `Classical.choice`, and `Quot.sound`.

This refutes only the extracted 11-vertex gate. It does not refute the full
singleton-lower `1+32` gate or the upper-singleton `41+1` gate.

## Route consequence

The local counterexample contains strong seven-sets, but the discarded upper
vertices were exactly the possible resource for promoting or charging those
witnesses to size eight. The next lower-tail contract must therefore retain:

- both cap-four-free sweep sides and their exact total size 32;
- their individual cardinalities in `11..21`;
- the unused vertices after selecting cup witnesses; and
- the recursive decomposition data needed to prevent repeated use of the same
  reservoir.

The first reservoir layer now compiles. Since every decomposable 23-vertex
restriction invokes the unconditional `(4,8,8)` theorem, it must contain a
four-cap when the parent avoids seven-cups and strong eight-sets. Greedily
deleting two such caps leaves 24 vertices, so Lean extracts three pairwise
disjoint upper four-caps. Parent five-cap avoidance forces all three caps to
straddle the singleton root, and 20 upper vertices remain unused. The open
combinatorial heart is to augment this decomposable, locally pairwise-disjoint
cap reservoir with an explicit tree-ownership argument that produces two
weakly separated caps. The existing singleton-root theorem would then extend
them to a forbidden five-cap.

The weaker statement that three selected disjoint straddling caps alone force
an outcome is false at the signotope level. A canonical 13-vertex instance
with three disjoint `2+2` caps is SAT; the independent checker verifies the
root crossing law, all three forced caps, and absence of every target. This
does not refute the 32-vertex density invariant or establish recursive
decomposability of the SAT model. It does rule out discarding the remaining 20
reservoir vertices after the Lean extraction.

The `41+1` tail remains separate. Small straddling-cup shortcuts have only
computational counterevidence so far; no Lean refutation of the full tail is
claimed. Route selection should compare reservoir-aware promotion with a
minimal-critical-root descent before freezing the next theorem contract.

## Reproduction

```bash
lake build ErdosSzekeres.StructuralChargingNextState578
lake build ErdosSzekeres.StructuralChargingNextState578Counterexample
python3 scripts/generate_rooted_cup_blocks_state_sat.py \
  --left 5 --right 5 --cap 5 --cup 7 --strong 8 \
  --output runs/state-578/rooted-cup-blocks-55.cnf
cadical -w runs/state-578/rooted-cup-blocks-55.sol \
  runs/state-578/rooted-cup-blocks-55.cnf
python3 scripts/check_signotope_state_witness.py \
  runs/state-578/rooted-cup-blocks-55.cnf.json \
  runs/state-578/rooted-cup-blocks-55.sol
```

SAT output remains computational evidence only; the separate Lean theorem is
the completed negative result.
