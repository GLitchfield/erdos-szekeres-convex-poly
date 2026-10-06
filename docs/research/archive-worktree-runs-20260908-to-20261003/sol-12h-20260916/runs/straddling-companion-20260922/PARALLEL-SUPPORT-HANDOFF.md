# Parallel Sol support handoff (2026-09-22)

The native Sol host `20260922-150750-451bdb` remains the only theorem owner.
Two user-requested Sol/xhigh support threads finished read-only research. Their
full reports are in the primary checkout:

- `runs/straddling-companion-20260922/parallel/coupled-recurrence/REPORT.md`
- `runs/straddling-companion-20260922/parallel/actual-cut-falsifier/REPORT.md`

The recurrence thread found a faithful actual-cut diagnostic with
`B.bound = 9`, low-pruning bound `6`, high-pruning bound `6`, and rank-pair
union cardinality `9`. Thus the tempting independent-pruning estimate
`low.bound + high.bound <= |union| + 2` is false (`12 > 11`). The loss persists
when the two source-cut descendants are each pruned by capacity color: the
actual descendant bounds are `6 + 3`, but their color-pruned totals add to
`12`. A proof of the direct `B <= 11` result must retain the two *unsplit*
actual source parts jointly through the cut recurrence, using complementary
maxima and the physical maximum-one marker before pruning.

The other thread tested repeated opposite history with corrected pruning
semantics. In its bounded domains it found no counterexample to the direct
`B.bound <= |pairs 0 ∪ pairs 1| + 2`; its largest residual bound was `8`.
It proposed Lean-sized support-order and maximum-one-join absorption lemmas.
The probe is diagnostic and covers neither arbitrary contexts nor all maxima.

These are mathematical leads, not compiled Lean theorems or proof receipts.
They do not change the native host's frozen deadlines or grant theorem credit.
