# R16 accepted inventory at 2026-10-01 10:52Z

Eleven independent helper theorems; each targeted receipt reports a locked type,
no holes and only propext, Classical.choice and Quot.sound.
Read-only verification confirmed every commit has exactly approved parent
5847e155fa613d4d2311eaee86b4b094f630e9a4. No integration was performed.
The checks below are the final accepted checks; failed attempts remain recorded
in the shared journal and detailed handoffs.

| Accepted result | Commit | Final targeted check | Locked type | Frozen evidence |
|---|---|---|---|---|
| Extreme-run-end weakening | cd1e05ce4528237b2cae5d120e310f044bcacdaf | 20261001-020205-1f077b | 6ecc666112a7ba4e | [PART1-HANDOFF.md](PART1-HANDOFF.md) |
| Exact boundary marker erasure | aab76b86245a78f2f5648b83ebb90931b2e9c4dc | 20261001-030155-fd7bff | 81fb6b0b14b6f62a | [HANDOFF.adjacent-marker-exact.md](HANDOFF.adjacent-marker-exact.md) |
| Capacity Pascal identity | 1839fee7b02a6d9d405b9dabf445025ea1f7772c | 20261001-032731-9e217b | 909643c533edfebe | [Capacity-pascal.closed.lean](Capacity-pascal.closed.lean) |
| Exact adjacent boundary merge | 4ad1c24f2cbc2b96d7263a9c20edcc1ff4ab6dec | 20261001-041119-280ff1 | 98bb67be7dd8f195 | [HANDOFF.adjacent-marker-exact.md](HANDOFF.adjacent-marker-exact.md) |
| Both-marked threshold lower, unrestricted axes | 52237b4bc87c167ee79ddab868f72687a48778a4 | 20261001-045854-d7ff87 | 3cc8ecb823117d12 | [HANDOFF.both-marked-point-lower.md](HANDOFF.both-marked-point-lower.md) |
| Global threshold upper, axis <=3 | 42e07c0555940b8c75cd9a6d46453b8be5d7d2c8 | 20261001-051403-870405 | 7b06c7ca92220a2b | [HANDOFF.small-global-threshold-upper.md](HANDOFF.small-global-threshold-upper.md) |
| Both-marked first-child selector, effective axis <=3 | 10301b1910f55bbc159cbf069865a9da9d29e1d2 | 20261001-053631-a4510e | c380b1b17be83d25 | [HANDOFF.both-marked-small-attainment.md](HANDOFF.both-marked-small-attainment.md) |
| Exact exposed-prefix marker merge | 338a9e2b92e93962cc1c83113c83ae56c839f83c | 20261001-054505-06eb5d | c499ac52f8ccd38 | [HANDOFF.unmarked-prefix-merge.md](HANDOFF.unmarked-prefix-merge.md) |
| Exposed-first/marked-last selector, effective axis <=3 | 19f3afb270ae9117fc03b0437fdb968eeb09fb57 | 20261001-060132-eada08 | c8e0da0d4fb01920 | [HANDOFF.exposed-first-small-attainment.md](HANDOFF.exposed-first-small-attainment.md) |
| Global threshold upper, axis <=4 | 9c1bbea3ad65cc50f3968b24ca393c6609180f87 | 20261001-060938-fe682e | 2d604b39265c45b4 | [HANDOFF.global-four-upper.md](HANDOFF.global-four-upper.md) |
| Both-marked first-child selector, effective axis <=4 | 969fbbaa55474f6aa839058758f75c90a499ac8b | 20261001-062838-278d13 | 3e9549000369df01 | [HANDOFF.both-marked-four.md](HANDOFF.both-marked-four.md) |

The weakening is conditional on the selector premise and does not import the open
N_ends constant. The Pascal and normalization theorems are reusable identities.
The selector theorems retain their stated legal global, marker and run hypotheses;
their axis restrictions are substantive. Full N_ends and N_root are still open.

The open N_ends registration is separate commit
22d8137334ce31f2175aee57f29ff79d92fc1f36, with a diagnostic falsifier.
It grants no closed-theorem credit. Its targeted check is
20261001-013617-679625, locked type 32c6d22aba01da18.

Two larger-axis charging routes failed on the same tested family. See
[HANDOFF.larger-axis-upper-stuck.md](HANDOFF.larger-axis-upper-stuck.md):
jobs 20261001-061913-2ecdcc and 20261001-062036-f1475c.
Those failures refute the proposed budgets, not N_ends or the tested upper bound.

Existing reflection was rediscovered at 10:48Z:
ctx_bound_reverse is already closed on the approved base, type 4125616738b08f1d.
Its application to the mirrored selector remains to be checked.

Current next-node branch job 20261001-063707-521ad6 is queued.
This inventory does not credit pending registrations, proofs, jobs or integration.
Exact source hashes were rechecked with sha256sum; the boundary hash correction is
preserved in ERRATUM.boundary-source-sha.md. Source and receipt details are in the
linked handoffs and REPORT.sol.md. No additional Lean build was run for this inventory.

