# Reflected endpoint-incidence matrix gate

## Question and review boundary

After both actual-ray event encodings failed, the Innovation Scout proposed a
linearization of the full reflected two-endpoint family. For each retained
span, use one row over the existing untagged ideal columns. The entry at an
ideal is zero, one, or two according to how many of the span's two reflected
endpoint intervals contain it. Linear independence would bound the number of
rows by the number of ideal columns and hence by the desired Pascal
coefficient.

A bounded review packet at SHA-256
`097dd1be3b15cc54a41d4157a5ac196ef8660e4860e43483ae84870a27559788`
compared this mechanism with two-lane meet/join uncrossing. Codex Sol returned
`partially_supported` at high confidence and selected exact rational rank as
the sharpest first falsifier; its result SHA-256 is
`053b0a0b8b76d2ef762ede1421acae22c1cb63f7207d3df3a0c1fab050bc30c4`.
Claude Fable returned a zero-token `ENOTIMP` provider connection error, so
there was no Fable judgment, reciprocal round, or model consensus. The review
is advisory route evidence only.

Laplace independently froze the same noncircular contract. Columns may not be
tagged by lane or orientation, and the coefficients may not depend on a known
matching. A rank defect stops this exact independence mechanism even when Hall
still holds.

## Exact matrix

For each span `s`, let `L_s` and `R_s` be its left- and right-endpoint lattice
intervals after applying the already formalized orientation reflection to both
lanes. For every untagged rectangular ideal `I`, set

    M[s,I] = 1[I in L_s] + 1[I in R_s].

The producer orders spans by the existing frontier enumeration and ideals by
their cell masks. It computes exact rank over the rationals and enumerates all
inclusion-minimal dependent row sets. Every circuit coefficient vector is
cleared to primitive integers with positive first coefficient and checked
against every column.

## Frozen refutation

The four frozen `n = 12`, `k = 7` frontier groups have row ranks

| group | rows | exact rank |
| --- | ---: | ---: |
| cap, rank 3 | 6 | 5 |
| cap, rank 4 | 2 | 2 |
| cup, rank 3 | 7 | 7 |
| cup, rank 4 | 4 | 3 |

Thus two groups are dependent although all four reflected candidate families
pass Hall. The cap/rank-three circuit is

    2 row(0,4) - row(4,6) - 2 row(6,10) = 0.

The cup/rank-four circuit uses all four rows, in frontier order, with primitive
coefficients

    (2, 1, -1, -2).

These are genuine signed relations, not merely repeated rows. Exact rational
row reduction in the producer and exact integer-minor/cofactor certificates in
the checker agree.

The compact manifest SHA-256 is
`2a7f083e9a2a41197218e25892567f300458a13254c49cd4e7bac6ebd7eee000`.

## Claim boundary and route consequence

This is bounded computational evidence, not a Lean theorem. It refutes
universal linear independence of this exact fixed `0/1/2` incidence row. It
does not refute reflected Hall, the local Pascal bound, every possible linear
or exterior-algebra argument, or a two-lane proof. Because the selected
mechanism fails on the same frozen root, no conditional Lean row-independence
bridge is promoted. Experiment 0035 tests the first precise adjacent
meet/join rule while retaining both endpoint lanes.

## Reproduction

    python3 scripts/check_reflected_endpoint_incidence_matrix.py \
      --output data/derived/e3-reflected-endpoint-incidence-matrix-frozen-n12-k7.json
    python3 scripts/replay_reflected_endpoint_incidence_matrix.py \
      data/derived/e3-reflected-endpoint-incidence-matrix-frozen-n12-k7.json
