# All-hole `k = 7` reflected lane-path certificate gate

## Question

Does the exact universal Lean lane-path contract survive every bounded
`k = 7` hole, including holes with no membership-feasible owner map? Does the
stronger exact singleton-neighborhood trace have an existential witness once
the first genuine two-gap paths appear?

Experiment 0048 selected shaped deficient anchors only for the 3,056 holes
having a feasible owner map. The Lean contracts quantify over every hole in
every nonempty consecutive block, so the other 2,419,060 holes required a
separate audit.

For each hole, the cell-mask producer and independent row-height checker
search both normalized endpoint lanes. A witness is a complete saturated ideal
interval with `m + 1` anchors, `m` distinct block-small owners containing its
adjacent gaps, and no other block-small owner meeting the interval. The
stronger search additionally requires every singleton anchor neighborhood to
equal exactly the owners of its incident path edges.

## Bounded result

Both implementations pass the complete gate.

| Quantity | Count |
| --- | ---: |
| Exact-rank frontier groups | 947,452 |
| Consecutive blocks | 1,830,286 |
| All hole checks | 2,422,116 |
| Feasible-owner-map holes | 3,056 |
| Zero-feasible-owner-map holes | 2,419,060 |
| Lane-path certificates | 2,422,116 |
| Exact singleton-trace certificates | 2,422,116 |
| Length-zero paths | 2,418,432 |
| One-gap paths | 3,170 |
| Two-gap paths | 514 |
| Path failures | 0 |

The deterministic first certificate has an exact singleton trace in
2,421,602 cases. Its trace is inexact in all 514 two-gap cases, but an
alternative exact-trace certificate exists in every one of them. This makes
existential selection essential and supplies the first bounded evidence for
paths longer than one edge.

The producer and checker agree on checked-prefix digest
`0b7f9c79c190c40766f21c72aef75e82499e0351842e204d7084e5fa118a6f26`.
The manifest SHA-256 is
`acf09031049232967e8ad4b7f45ad6b8319c0543773f1c2419cde1ca4a438362`.

## Review and claim boundary

A bounded blind review used evidence-packet SHA-256
`fbc83f02526a8be8dcfd15e90ffeb323f8164427a07cca03ceaf574019fcffe2`.
Sol returned high-confidence `partially_supported` and selected falsification
before direct geometry, with exact singleton traces as a conditional local
constructor. Fable returned no mathematical answer because its provider usage
limit was exhausted. No Sol/Fable consensus is claimed.

This remains bounded computational evidence for `k = 7` through support size
eight. It does not prove the arbitrary decomposable geometry contract, Hall,
an SDR, or the exact Erdős--Szekeres formula. Lean separately proves that
local neighborhood containment constructs a path certificate, that exact
singleton traces are a sufficient strengthening, and that rank one is
vacuous. The open theorem is to derive an exact trace witness from
decomposable deep-split geometry, with rank two handled directly and the
active-ray argument beginning at rank three.

## Reproduction

    python3 scripts/enumerate_lane_path_certificates_all_roots_k7.py \
      --maximum-n 8 \
      --output data/derived/e3-lane-path-certificates-all-roots-k7-n8.json
    python3 scripts/check_lane_path_certificates_all_roots_k7.py \
      data/derived/e3-lane-path-certificates-all-roots-k7-n8.json
