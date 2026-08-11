# Experiment 0092: state-567 and diagonal certificate feasibility

Date: 2026-08-10

Status: Kernel-checked CNF certificates; semantic bridge open

## Question

Can the first open diagonal `k = 9` cup-block gate or one exact state-567 cut
be promoted through the repository's LRAT workflow within the current resource
limits?

## Certificate results

Both normalized `k = 9` dense cores check directly with mathlib's LRAT
checker:

| Orientation | Variables | Clauses | LRAT additions | Lean time | Peak RSS |
| --- | ---: | ---: | ---: | ---: | ---: |
| `7+8` | 396 | 1,157 | 812 | 3.01 s | 1,268,548 KiB |
| `8+7` | 280 | 429 | 239 | 1.15 s | 993,288 KiB |

Their axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. The checked objects prove the selected propositional formulas
UNSAT; they do **not** yet prove `DiagonalCupBlocksForce4kk 9`. A generated
Lean bridge must still show that `OneChangeOn`, the two forced cup blocks, and
the target-avoidance hypotheses imply every retained clause, and then
transport the normalized `Fin 15` theorem to arbitrary ordered blocks.

The cut-7 state-567 dense core has 5,499 variables, 39,809 clauses, and 46,718
LRAT additions. Independent streaming RUP replay passes, including a corrupted
hint negative control, but a monolithic Lean import exhausted the 8-GiB limit.
Dependency analysis estimates eight checkpoints as a conservative import.
Even after that engineering step, cut 7 would close only one of the required
22-point cuts and would still need a much larger semantic bridge, including
the XOR definitions for middle-color comparisons.

## Route disposition

`K9_CERTIFICATE_GO__SEMANTIC_BRIDGE_NEXT;
CUT7_CERTIFICATE_CHECKPOINTABLE_BUT_SECOND_PRIORITY`.

The exact next theorem is

```lean
theorem diagonalCupBlocksForce4kk_nine :
    DiagonalCupBlocksForce4kk 9
```

The next completed result must include the generated semantic clauses and
normalization/transport proof. Solver output, independent replay, and a
kernel-checked bare CNF refutation are supporting evidence, not that theorem.
The balanced state-567 branch still has five distinct leaves; no compiled
order-reversal bridge currently merges them.

## Reproducibility and limitations

- Structured result:
  `runs/agents/20260810-three-route-forward/state567/result.json`
- Result SHA-256:
  `43ca26d6e7fc2f2c780b1626a345dbf1893585b74e75d6df295bed3f47234fa9`
- Dense `7+8` CNF/LRAT SHA-256:
  `ed5d3604a251013d80716f2cff0f0d7eb34a81936bcf281792f39b56a839fe72` /
  `47654921221546d883544620525cb98806238d65f112467f9ccfe10dfafa0c8a`
- Dense `8+7` CNF/LRAT SHA-256:
  `21c281818b3688488debe1d521b6f4b468c2d34a2d79db8a3a7962a7ab679d39` /
  `150596401f45f9789deaba920e0e87690eceb5c68ad8524e2ac7611bd3544091`
- Dense cut-7 CNF/LRAT SHA-256:
  `0b65f44fd4b96f922dcf3ee6dd4f6061e7db88b221c2411dc35a6cbd660a5dc4` /
  `22238c1ba44dc7df435ae1cd57d977bd46b72df29d979ef6e50849e5f6ca26f3`

The interrupted cut-11 trace was never independently verified and is excluded
from every claim.
