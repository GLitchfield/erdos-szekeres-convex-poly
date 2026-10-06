# R13 report — STUCK, finalized 2026-10-01

**Done is not met. C1r remains open and unchanged.** Research stopped under
the brief's two-failed-attempt rule. All authorized helper/compiler/probe /
library jobs are terminal; no new trial is being started.

The coordinator reviewed and accepted this STUCK result, ending research at
2026-10-01T00:00:34.307053Z. The finalization hard stop is
2026-10-01T00:30:34.307053Z. Evidence is host/FINISH-REQUEST.json and
host/agent-run.json; this turn only inspected existing evidence and updated
reporting/accounting. No new research or checks were launched.

Five reusable Lean nodes have unchanged statement locks, sorry=false and
only standard axioms (propext, Classical.choice, Quot.sound). Each node was
committed on its own branch from main41cc0e4b:

| Result | Commit | Targeted check job |
| --- | --- | --- |
| singleton part equals explicit T | 6d49410067fbc677ae64cc252d4774698985c353 | 20260930-165717-642558 |
| raw run count preserved by adjacent deletion | 5bfb2e085e2999b10be2bf31fedfd645eb1fb152 | 20260930-173003-dade47 |
| unit global axis gives zero at every fuel | dd4291f419eef48178c2c75d9e839b6de18defa3 | 20260930-175052-dd087d |
| singleton attainment with <=3 children | 59809ac4e015f79f8acd2b58ccf07bd60d7257f1 | 20260930-183003-64cb4c |
| exact one-level extension/capacity formulas | 95559e090ff7044040348aec1c00ac7094fbd6af | 20260930-194307-536ecb |

The last node also passed isolated op-489128753867417b /
20260930-192528-c4309b,12.04s/2101MiB. Its installed source matches the
accepted candidate SHA81e034f2 exactly; only the captured proof body changed.
Targeted build5.13s/649MiB, unchanged type27c5ffa48b789810,lock_ok=true.
All five helper claims are released closed. Focused helper handoffs give
exact raw hypotheses, axioms, source hashes and receipts.

The strictly narrower exchange X is registered and committed at
eb65ce22ba759254ff4db4a06a159c5e70bd6f78 but remains sorry/open. Its guarded
falsifier20260930-171455-ff2d9f passed106912cuts/168592explicit-T audits.
Full C1r composition compiles in scratch from BOTH N and X
(20260930-185428-a5469d), and from X with <=3 children
(20260930-185653-ed8b9e). These are not registered full C1r-from-X alone.
The exact missing lemma for this route is root singleton attainment N at
arbitrary child count; no reduction discharging N was proved.

Minimum active-capacity selection failed in20260930-175945-5d3b66.
Fixed-position leaf lifting failed in20260930-191222-5c7678: a legal inner
cut2 plus outer rest1 totals3, while every root singleton at that same p
has value<=2. A different p attains3. These witnesses refute the attempted
routes, not N or C1r. MATHEMATICAL-HANDOFF.md supplies exact contexts and
hypotheses. No larger retry of either false candidate was run.

Final diagnostic20260930-184927-794b43 passed all95232rows, all31distinct
multi-run four-child/three-occupied-level placements at(5,5,6),eight side
patterns,six orders,64maxima: complete=true,zero failures,3935.7s/334MiB.
General five-child diagnostic20260930-170246-ccbdbe passed3889rows,
8236.3s output time. Probe scope restrictions are recorded in the handoff;
finite arithmetic evidence is not a Lean theorem.

Recurring singleton-cut enumeration was retained in the library in separate
commit8fd0a9b8efa3325f492cfb952f810ed9b1b200a4. Guarded regression
20260930-192820-7a8919 passed10tests; catalog example
20260930-192847-4fa726 passed. CODE-REVIEW.md records Sol self-review and
source/inline-command inventory. The coordinator has now reviewed and
accepted five closed helpers and registered X. This is distinct from the
recorded Sol code self-review; no additional model or delegation was used.

Recorded all-in thread usage, including setup and failures, is in
USAGE.finalization-sync.json; two local window reports and FACTUAL-HANDOFF files
preserve accounting boundaries. Active/later requests may lag. The host
review's usage import was refused because requests already had explicit
local-window assignments; its zero count is unavailable accounting, not
zero cost. No matched-baseline savings claim is made.

Integration was verified read-only against main 7d9c2fed: the first four
helpers are closed there and registered X remains open. The accepted fifth
helper, ctx_single_level_limits_exact at 95559e09, awaits integration by
the coordinator. That is the safest next action; the coordinator has
prepared R14 for the remaining N_root obligation. R14 was not started here.
These integration facts do not supply a full C1r proof receipt.
The only tracked residue is the fresh
passing C1r falsifier result, intentionally excluded from other nodes'
commits. No merge/push, primary-source edit, existing-statement edit, full
extraction, new axiom or native_decide. The native goal remains paused and
incomplete because C1r and the required full reduction remain unproved.
C1r is released
partial with the mathematical handoff; no unattended notification is promised.

Finalization review receipt REVIEW.finalization.json references immutable
7e3af45718ba52622650b827a08076f89e6728ff583511e8da7d103c3a7b1a34:
94 jobs, pending=0, unknown=0, active R13 claims=0. It grants no theorem
credit; the five named targeted checks above support the helper claims.
MAIN.integration-finalization.txt preserves the read-only integration check,
and LOG.finalization.json records this final account in the shared journal.
