# Accepted exact diagonal gate

2026-10-03T04:50Z. The exact requested
`singletonLowerPascalTailGate_five_diag_of_six_le_of_inputs` is accepted
and committed at `5d4fa26d8a20192c90624b23ed8a9cef90af8dd1` on
`node/SingletonLowerPascalTailGateFiveDiagOfSixLeOfInputs`.

Full original-source check `20261003-002634-6a5ff2` took 1284.1 seconds,
peak 5670 MiB. `diag-gate-original-source-receipt.json` confirms CLOSED,
exact locked hash `87bbef437ea7141f`, no sorry and only
`propext`, `Classical.choice`, `Quot.sound`. Audit of 25 changed
declarations is clean. Capture `20261003-004855-2c9cd8` saved fixture
`7ac8e061d29029089b5b7affd65d074b1d2527edf7510f17aeff910d85acf26f`.
Commit job `20261003-004916-0f0642` completed successfully.

The proof takes the exact uniform R20 cupblock and R21 Baek theorem
shapes as explicit hypotheses. It derives their fixed-k pair and
single-set bounds; the final Pascal term raises the predecessor
reservoir to G+1, where G=C(k-1,2)+C(k-3,2)+1. The singleton lower
point supplies a gap whose sides avoid four-caps. A root split of the
upper set supplies decomposable children, and the accepted full
diagonal root bound G contradicts its reservoir cardinality G+1.

The root proof and reusable R1/R2/deficit tools are documented in
`MATHEMATICAL-HANDOFF.md`, `DIAGONAL-PROOF-PLAN.md` and
`MATHEMATICAL-REVIEW.md`, with their original-source receipts and
commits. Root commit is `2bce9cc2f6b0b99005852f82285bf7ce35f56940`;
predecessor gate commit is `0281d8bbf6ec782323840a4c2643153a648124fb`.
No mathematical case or hypothesis was narrowed. Wrapper source
compiled first try in `20261003-002559-692f37`.

Remaining authorized work: optional upper gates via the existing
colour-dual iff, final separate mathematical/code review and usage
reconciliation, and consolidation before the fixed research deadline.
The diagonal input theorems still require coordinator instantiation
after integration; this run deliberately preserves baseline 6e4d0e66
and imports neither R20 nor R21 proofs. The overall happy-ending
conjecture remains open. No new mathematical obstruction remains for
the two requested lower gates.
