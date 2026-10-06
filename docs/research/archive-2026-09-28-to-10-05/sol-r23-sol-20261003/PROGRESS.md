# R23 final progress

Research stopped at **2026-10-03T13:51:14.586618Z** by coordinator direction:
all resources go to generalization; the single `(6,k-2,k)` gate is no longer
a target. Finalization hard stop: **2026-10-03T14:21:14.586618Z**.
No new proof work was admitted after the cutoff.

The lower gate is **OPEN**, lock `135fffe38adb53ba`, scaffold commit
`9db1872a8a1dedd11a24ea740af48eaed5ef0dc6`, with authorized ESBlueprint
sorry. All thirteen root rows and the optional upper dual remain unproved.
Run/report completion does not close the gate.

Proof understanding: a cup ending where a cap starts extends one of them.
Cap-start peeling therefore gives a cap-free complement and smaller-cup-free
start family, explaining Pascal induction and gap localization. The remaining
gate obstacle is uncompiled asymmetric marker counting and root case analysis.

The requested general results compile at exact locked types without sorry,
using only standard axioms. All source checks are DONE rc0:

| Result | Commit | Original-source check |
|---|---|---|
| Generic cap-start peel | `e9d72dc51b48feb3e18189b2582af988c5eb920a` | `20261003-082029-56f844` |
| Classical OneChangeOn binomial bound | `bad5a94efe907f9d19352826904be0df34d8cdb9` | `20261003-085553-e4194e` |
| Z6 | `60bae7a83376f216b4baca5edcd7819b9270bbe5` | `20261003-090056-567700` |
| ZR/cup-prefix | `531f795cbb90671fcfa4751a1e1e32ef3c0c1b93` | `20261003-090944-96c6e4` |
| Threshold identity | `1cb1c58802cab020dc335eba4ace60d27007af1b` | `20261003-082944-f198ab` |

[MATHEMATICAL-HANDOFF.md](MATHEMATICAL-HANDOFF.md) supplies exact hypotheses,
locks, receipts, auxiliary results, failures and unresolved rows. It explicitly
distinguishes the threshold theorem from its uncompiled gate-wrapper use.
No final whole-project rebuild is claimed.

Current branch `node/CardLeChooseCubicOfOneChangeAsymmetricGapStraddledCups`,
HEAD `6008c8327606ea3a4d55b96fb5160a2a1ab84fd8`. Registration
`20261003-095112-7e4316`, submitted before cutoff, safely finished during
finalization. It creates only an OPEN scaffold, lock `9e3423b55839fa99`;
no proof check followed. The new module, import and generated registry/lock/
status edits remain uncommitted. Draft bodies supply no proof credit.
R21/R22 branches were preserved; no merge or push.

Existing-artifact review `20261003-095508-d25408` is DONE rc0, immutable
inventory `c7cb92d6c849439ad1da4e42bff7f8f8155a329e89d2e42897e7af15b2bf6fe3`.
Shared proof APIs were reused; no standalone workflow script or new library
algorithm was added. Review scope and limitations are in the handoff.

Research window `window-a94d596de85d45f0` is administratively closed; effective
end remains the earlier coordinator cutoff. Separate finalization window:
`window-058a20a897e74372`. Usage import `20261003-095824-10c84e` is DONE rc0,
reconciled through 13:58:23.677Z; active/later reporting can lag. The native
observer's unavailable usage coverage is not a zero-cost claim.

Final gate claim release is **PARTIAL**, confirmed by `final-gate-release.json`.
`final-status.json` reports OPEN/sorry=true, no live claim, no stale index and
no problems. The release's immutable handoff snapshot is
`a41a6e70895cd3d470816b1ea245e11b4181a1a5e30b2b9e31f8fa4477105890`;
it preserves this worktree document without overwriting the different primary
checkout copy. Use the final worktree file and shared journal absolute path.

Final accounting job `20261003-100442-929080` is DONE rc0. Both administrative
windows are complete; finalization accepts zero new results. The reconciled
snapshot covers 341 recorded requests through 14:04:41.755Z. Files:
`research-usage-final.json`, `finalization-usage-final.json`,
`finalization-window-end.json`, `research-factual-handoff.json`,
`finalization-factual-handoff.json`. Active/later reporting may lag; resource
coverage excludes unlinked jobs. Initial finalization predates administrative
research-window closure, so no exact research/review cost split is claimed.

The requested final report is supported by the inspected commits and compiled
receipts. Completing the native lifecycle is administrative completion of the
coordinator's revised handoff scope; it cannot imply gate closure. Next
authorized action: generalization using the generic peel and classical bound.
Do not automatically restart this retired gate trial.

Native goal status **COMPLETE**, verified at 14:06:11Z, for the coordinator's
revised finalization/report scope. This does not assert the original gate
was proved. Native counter: 948,479 tokens; 6,284 seconds (about 1h45m).
`final-status-verified.json` again reports OPEN/sorry=true, no own live claim
or job, no stale index and no problems. Finalization finished before hard stop.
