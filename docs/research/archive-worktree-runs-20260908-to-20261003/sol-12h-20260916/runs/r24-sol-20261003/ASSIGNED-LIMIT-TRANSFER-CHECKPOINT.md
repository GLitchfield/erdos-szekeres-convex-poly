# General assigned-limit transfer — historical validation checkpoint

SUPERSEDED 2026-10-04 01:10 UTC by `ASSIGNED-LIMIT-TRANSFER-ACCEPTED.md`.
All five normal stages succeeded and commit
`e0e315251ec3aa17aeb7165ff1b87f6e9aa82396` completed. The automatic CLOSED
release and clean tracked worktree are verified. The pending descriptions
below preserve the historical validation state; they are not current.

Update 2026-10-04 00:50 UTC: normal candidate `203730-c501f1` and original
source `203745-53f704` passed. Source stage took 61.927 seconds/2356 MiB,
targeted=true/incremental=true, CLOSED/noSorry/standard axioms/lock_ok=true.
Receipt `1ba02afefc7f0c7f111c6a36372c0c861e8c94c29059726d61481bb08158aead`.
The exact original source and body hashes match the isolated receipt.
Full extraction `20261003-203849-0c96ab` is the only owned pending job;
audits/review are dependent pending stages. At the ten-minute checkpoint,
module scan 15836/15836 was complete but later validation remained active;
measured comparable full stages imply roughly 9–21 minutes remaining.
`assigned-transfer-full-review-10min.json` records leaving it running.
Inventory refresh was refused before creation at the shared 40 GiB cap;
defer it until full extraction releases its reservation. No cap or policy
change, cancellation, full closure or commit is claimed.

2026-10-04 00:38 UTC. Branch `node/CtxAssignedLimitsOfDeepBelowSplit`
from `aebb65051bc97c57ca9c3da83f42c7533f66e3a1`. Registered theorem
`ErdosSzekeres.ctx_assigned_limits_of_deepBelowSplit`, locked type
`a89e497ebd1cfbea`, normally claimed after full ready=true/lock_ok=true.
The exact type is `assigned-limit-transfer-node-type.txt`; all hypotheses
remain unchanged. Module `ESBlueprint.B.CtxAssignedLimitsOfDeepBelowSplit`.

For any actual deep-below split, monotone assigned labels, unequal labels
across children, explicit new-level sides and opposite-marker membership,
and shares α+β=k−1 with k≥3, complete child cup/cap endpoint bounds and
child strong-k avoidance imply the corresponding parent bounds and
parent strong-k avoidance. Empty chains are included. There is no slot
occupancy, label-range, WF, placement or cardinality assertion.

The proof inherits pure limits, selects 0/1/2 strict opposite endpoints,
and transfers their cardinal gains using the accepted path-count theorem.
The finite-endpoint criterion handles all crossing cups; caps follow by
duality. Zero-gain child limits give lower cup≤α and upper cap≤β, so the
accepted strong-composition criterion closes the parent crossing case.

Registration `20261003-203310-9b9d69` passed, 132.5 seconds/2308 MiB.
Capture `20261003-203554-5988fa` passed; fixture
`882acc574ffd0e7c77c2341e2ea0b88de088dd86421b7556ce8791ddb9d2f27d`.
The first actual v3 check `op-c691f2f7a07a4f42`, job
`20261003-203616-0f6583`, failed five API/binder/subset elaboration errors;
receipt `08cfb498`, complete diagnostic `4bdcb0cd` are preserved.

V4 `op-cc803803035349f6`, job `20261003-203659-a14e3c`, passed isolated
checking, 11.65515 seconds/2103 MiB, unchanged type and only propext,
Classical.choice and Quot.sound. Receipt
`cbf0621724bc105537d617d20b91f551fe9cfba9f8cd814aa6cc71bc74142f34`;
body `4cc583c66c38c58ae3a55165057c006afe702b2b3bdec669208e8574d1144b60`;
source `adfe71d0ae78c36d471a611c8dcfb9512e8d5971eadb986e933cd651e86abc47`.
The complete success diagnostic `fba537e7` was read.

Shared closure measurement `20261003-203627-e03aa5` passed:
0.056484 GiB, missing=[], fits the existing 4 GiB targeted eligibility.
This is eligibility evidence, not a peak-memory guarantee.
Normal node-finish `op-e4fb2f1518694e80` is RUNNING with review policy,
original-source and full-extract/audit/review stages still required.
No full closure or commit is claimed. Initial candidate job
`20261003-203730-c501f1`; inspect operation state for subsequent job IDs.

Research window `window-164c4bd3540947a3`. Follow-up: inspect all terminal
receipts, exact source/body/type, fresh frontier, audits and complete review
diff; make one-node local commit and verify claim release. Then perform a
separate fixed-Sol source/code review and reconcile usage. No further trial
is planned. Stable placement and exact fuel induction remain the explicit
B-attainment obligations; the upper endpoint-loss invariant remains open.
