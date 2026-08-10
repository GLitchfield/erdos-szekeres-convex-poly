# Experiment 0091: state-567 packed branches and diagonal k=9

Date: 2026-08-10

Status: Computationally supported; no formal closure

## Questions

Do the two exact packed obligations retained by the state-567 reducer admit a
countermodel, and does the diagonal `DiagonalCupBlocksForce4kk` interface
survive its first new case `k = 9`?

## Bounded state-567 audit

Exact middle-determinacy SAT instances for all nondual split representatives
on 22 vertices were UNSAT:

| Cut | Variables | Clauses | Solver time |
| ---: | ---: | ---: | ---: |
| 7 | 42,068 | 493,523 | 14.566 s |
| 8 | 42,068 | 493,194 | 90.487 s |
| 9 | 42,068 | 492,964 | 276.312 s |
| 10 | 42,068 | 492,828 | 414.888 s |
| 11 | 42,068 | 492,783 | 543.762 s |

Cuts 12--15 follow by reversal from cuts 10--7. These instances omit the
additional packed hypotheses, so their UNSAT status supports both packed
contracts. However, the run produced no DRAT/LRAT certificate and no Lean
proof. Under the project evidence standard, neither packed obligation nor
`TwoCapFreeSidesBound567` is completed.

The audit nevertheless identifies smaller structural leaves. The internal
branch can be reduced to one explicit mutually middle-obstructed pair of
strong six-witnesses, eliminating the universal packing quantifier. The
balanced `11+11` branch reduces to five explicit terminal witness classes:
crossing strong-six profiles `2+4`, `3+3`, or `4+2`, or one of the two
oriented three-residue pair-overlap packages. These are Lean-shaped proposals,
not declarations compiled in this run.

## Diagonal k=9 audit

Both normalized orientations were UNSAT:

- `7+8`: 455 variables, 658,021 clauses, 27.523 seconds;
- `8+7`: 455 variables, 658,021 clauses, 27.707 seconds.

Each CNF was regenerated independently with byte-identical hashes. Again, no
checked UNSAT certificate was produced, so `DiagonalCupBlocksForce4kk 9`
remains formally open. The evidence supports continuing the diagonal symbolic
proof family but does not replace the state-567 obstruction.

## Route disposition

`PACKED_567_REDUCED_NOT_CLOSED__K9_UNSAT_NO_CERT`.

The main uniform Pascal route remains blocked at the first open state-567
geometric gate. The computation substantially raises confidence that the
gate and the `k=9` diagonal instance are true, while the next completed result
must be a compiling structural proof or a kernel-checkable UNSAT certificate.

## Evidence

- `ErdosSzekeres/StructuralChargingWitnessBranchesPacked.lean`
- `ErdosSzekeres/StructuralChargingPascalCupBlocks.lean`
- ignored structured result
  `runs/agents/20260810-next-four-hour-block/pascal-567/result.json`
- result SHA-256
  `50a95a360cc060d8a83b8f2c829c5b179d58740a21081363e8a9884e43e3cdee`
