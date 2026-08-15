---
title: Formalize the first Ringel-nine nonstretchability boundary
type: research
mode: AFK
status: closed
claim: codex-ringel-nine-nonrealizable-2026-08-15
blocked_by: none
---

## Question

Can the authenticated Ringel uniform rank-three nine-element class be excluded
from sweep-realizable colorings by an exact Lean proof, and does that exclusion
close a full-context state-567 terminal?

This ticket separates two obligations that earlier computational work had
conflated:

1. prove the fixed Ringel representative nonrealizable for arbitrary
   homogeneous vectors in `R^3`, including all relabeling and reorientation
   semantics; and
2. prove that the full packed/provenance state-567 context produces such a
   restriction or otherwise consumes its exclusion.

The first is a local geometric theorem.  Only the second can strictly reduce
the state-567 subordinate obligation of `D-DECOMP`.

## Decision criteria

- Authenticate the exact 84-sign representative and source license before
  using it.
- Require a compact exact final-polynomial certificate and an independent
  checker with coefficient, sign, omission, relabeling, and final-cycle
  corruption controls.
- Do not state unconditional nonrealizability in Lean until that independent
  gate passes.
- Formalize arbitrary homogeneous rank-three vectors, not a chosen affine
  chart or rational-coordinate search.
- Keep increasing ambient selection distinct from arbitrary Ringel-label
  permutation, element reorientation, and global sign.
- Count the state-567 branch as reduced only if a theorem with the retained
  full packed/provenance or decomposable context compiles.
- Stop a consumer on a frozen encoding/checker convention mismatch instead of
  adapting it after seeing a model.

## Resolution

The local theorem landed; the global consumer did not.

1. **`R9-CERT-EXACT` (`computational_evidence`).**  The archived official
   Fukuda--Miyata--Moriyama OM(3,9) asset contains a 59-row biquadratic final
   polynomial for its unique uniform nonrealizable record.  Exact producer and
   independent checks validate all Grassmann--Pluecker rows, 354 positive
   displayed brackets, the 118-factor equality, and the full 84-sign transport
   to the frozen Ringel representative.
2. **`R9-VERIFY-EXACT` (`computational_evidence`).**  A separately frozen
   strict-cycle checker initially exposed a schema mismatch and then one
   list-versus-tuple implementation defect.  Both failures are preserved.  A
   final packet changed only `sorted(factor)` to `tuple(sorted(factor))`, proved
   that one-expression source diff mechanically, passed a first-row smoke
   gate, accepted all 59 rows and the nonempty balanced cycle, and rejected all
   six prefrozen corruptions.
3. **`R9-BRIDGE-LAND` (`file_compiles`).**
   `RankThreeBracket.lean` proves the rank-three bracket identity,
   homogenization, full reorientation transport, and the
   `IsSweepRealizable` realization bridge.  `RingelNine.lean` fixes the exact
   restriction semantics.  `RingelNineNonrealizable.lean` rederives every
   certificate inequality in Lean and proves
   `ringelNine_not_rankThreeVectorRealizable`,
   `IsSweepRealizable.noRingelNineRestrictionOn`, and
   `IsDecomposableOn.noRingelNineRestrictionOn`.  Direct Lean, targeted Lake,
   deterministic generation, style, forbidden-token, and axiom gates pass.
4. **`R9-FILTER-MISMATCH` (operational stop).**  The layered state-567 family
   formula was independently reconstructed and solved SAT, but its prefrozen
   semantic checker mapped the CNF Boolean convention to the opposite turn.
   The assignment was therefore not admitted, no Ringel scan or later layer
   ran, and no full-context theorem was claimed.

The local nonstretchability boundary is a real reusable theorem.  It changes no
load-bearing destination edge because no retained state-567 producer forces a
Ringel restriction.  The old catalog-only uncertainty is gone; the remaining
mathematical obligation is not another certificate or scan but a full-context
producer or consumer theorem.

## Evidence

- `ErdosSzekeres/RankThreeBracket.lean`
- `ErdosSzekeres/RingelNine.lean`
- `ErdosSzekeres/RingelNineNonrealizable.lean`
- `runs/agents/20260815-ringel-nine/certificate/result.json`
- `runs/agents/20260815-ringel-nine/verification/result.json`
- `runs/agents/20260815-ringel-nine/verification-adapter/result.json`
- `runs/agents/20260815-ringel-nine/verification-replay/result.json`
- `runs/agents/20260815-ringel-nine/lean/result.json`
- `runs/agents/20260815-ringel-nine/consumer/result.json`

## Resource and scope record

- Certificate discovery and producer checking stayed below one minute of
  arithmetic work after source retrieval; the independent exhaustive
  preflight/replay used about 31 seconds per gate and 30 MiB RSS.
- The final Lean certificate directly elaborated in about 15 seconds and the
  targeted Lake module built in about 14 seconds, both below 2.6 GiB RSS.
- The consumer's first SAT layer solved in about 40 seconds at 3.83 GiB RSS,
  but its assignment remains inadmissible because of the frozen convention
  mismatch.
- No result here characterizes rank-three realizability, proves state 567, or
  improves the exact Erdős--Szekeres upper bound without a separate producer.
