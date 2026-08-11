# Experiment 0098: diagonal `k = 9` semantic certificate

Date: 2026-08-10

Status: Exact diagonal theorem compiles

## Question

Can the two reduced `7+8` and `8+7` LRAT refutations be connected to the
repository's actual cup-block predicates and then transported from `Fin 15` to
arbitrary ordered blocks?

## Completed Lean theorem

The generated semantic bridge proves every retained clause from one of the
following exact hypotheses:

- the rank-three one-change law;
- absence of a four-cap;
- absence of a nine-cup;
- absence of a strong nine-set;
- the two forced cup blocks.

Both normalized contradictions and both arbitrary-block transports compile,
yielding

```lean
theorem diagonalCupBlocksForce4kk_nine :
    DiagonalCupBlocksForce4kk 9
```

with no `sorry`, `admit`, unsafe axiom, or unverified external oracle. The
Python generator and checker are reproducibility aids; the mathematical trust
path is the generated Lean clause proofs followed by mathlib's LRAT checker.
After the serialized integration build, the final theorem's axiom audit lists
only `propext`, `Classical.choice`, and `Quot.sound`.

## Certificate shape

| Orientation | Variables | Retained clauses | LRAT additions |
| --- | ---: | ---: | ---: |
| `7+8` | 396 | 1,157 | 812 |
| `8+7` | 280 | 429 | 239 |

The bridge is split into compact cap, cup, and strong encodings plus 24
semantic-clause chunks. This avoided the initial combined-file allocator
failure. The largest compact encoding check used 2,948,532 KiB RSS; the final
certificate target used 2,270,568 KiB.

## Independent replay

An independent checker reconstructs the complete 658,021-clause source stream
for each orientation, reverses dense variable renaming, matches the retained
clause multiset, replays every RUP addition, derives the empty clause, and
rejects a corrupted final-hint control. Five generator unit tests also pass.

The deterministic aggregate digest of the 38 generated Lean/certificate
artifacts is

```text
be72ec182adb45c2c81baf3d2af8da5c7409e0f7c1daa4167bce53f4791dd2ae
```

Certificate hashes:

- `7+8` CNF:
  `ed5d3604a251013d80716f2cff0f0d7eb34a81936bcf281792f39b56a839fe72`
- `7+8` LRAT:
  `47654921221546d883544620525cb98806238d65f112467f9ccfe10dfafa0c8a`
- `8+7` CNF:
  `21c281818b3688488debe1d521b6f4b468c2d34a2d79db8a3a7962a7ab679d39`
- `8+7` LRAT:
  `150596401f45f9789deaba920e0e87690eceb5c68ad8524e2ac7611bd3544091`

## Route disposition

`K9_SEMANTIC_CERTIFICATE_PROVED`.

This is the first new case beyond the symbolic diagonal theorems for
`5 ≤ k ≤ 8`. It validates the uniform cup-block interface and the generated
certificate workflow at `k = 9`, but it is not itself an induction from `k=9`
to every larger `k`. The decomposable E3 frontier still contains the exact
state-567 two-cap-free-sides obligation and needs a uniform structural
consumer or a separately certified terminal reduction.

## Evidence

- `ErdosSzekeres/DiagonalCupBlocksK9Certificate.lean`
- `ErdosSzekeres/DiagonalCupBlocksK9Normalized.lean`
- generated `DiagonalCupBlocksK9*Encoding.lean` and clause chunks
- `scripts/generate_diagonal_k9_lean.py`
- `scripts/check_diagonal_k9_semantics.py`
- `scripts/test_generate_diagonal_k9_lean.py`
- `certificates/k9-cup-blocks-*-dense.{cnf,lrat}`
- structured result:
  `runs/agents/20260810-parallel-portfolio/k9/result.json`
