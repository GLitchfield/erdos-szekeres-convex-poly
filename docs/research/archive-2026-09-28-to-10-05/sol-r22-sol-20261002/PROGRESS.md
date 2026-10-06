# R22 progress

Updated 2026-10-03T11:40Z. Agent `codex:agent-run-c94853b9754648ba`;
thread `01a0fefb-d883-7cc1-8d31-dc8f00948974`.
Native goal COMPLETE at11:40:33Z after supported final review; goal API
records3803401 tokens over43199 seconds. Late reporting is separately
preserved in usage-late-finalization.json with its snapshot caveat.
Research deadline 2026-10-03T11:38:33.055867Z; consolidation11:08:33Z.
Only configured Sol; no delegation, merge, push or cherry-pick.
Fixed baseline `6e4d0e66274e9d3dd1ccdbacf9fd747deb5e1d14`.

Both required lower gates and both optional upper gates are ACCEPTED,
committed and released CLOSED. No proof job or claim remains active.

| Target | Original-source check | Commit |
| --- | --- | --- |
| (5,k-1,k) lower gate, k>=6 | `20261002-223942-093363` | `0281d8bbf6ec782323840a4c2643153a648124fb` |
| (5,k,k) lower gate with exact uniform R20/R21 inputs | `20261003-002634-6a5ff2` | `5d4fa26d8a20192c90624b23ed8a9cef90af8dd1` |
| (k-1,5,k) upper gate | `20261003-010620-a45c42` | `cb87071e20d5a1199e014e943c267ddd729d357a` |
| (k,5,k) upper gate with the same inputs | `20261003-013823-62cacb` | `c79e55d04dffaa123194174c3a282374132654c2` |

All four exact locks match; no sorry; only propext/Classical.choice/Quot.sound.
Receipts `pred-gate-original-source-receipt.json` and
`diag-gate-original-source-receipt.json`. The diagonal full check took
1284.1s,peak5670MiB. Its fixture is
`7ac8e061d29029089b5b7affd65d074b1d2527edf7510f17aeff910d85acf26f`.

Proof idea: gap sides avoid four-caps by extension with the singleton.
Cup/cap coupling at a decomposable root forces smaller lower cup sizes.
Triangular/square bounds and sharp prefix/three-cup deficits bound the
predecessor root by H=C(k-1,2)+C(k-3,2), and the diagonal root by G=H+1.
Their singleton reservoirs are respectively H+1 and G+1, contradictions.
All orientations and the sharp k6 cases are certified. No mathematical
obstruction remains for the two requested lower targets. The global
conjecture remains open; diagonal inputs require coordinator instantiation
after integration.

Upper predecessor(k-1,5,k) is ACCEPTED and released CLOSED. Full check
`20261003-010620-a45c42`, hashf3116a1be4927653, no sorry, standard axioms;
895.4s,peak5655MiB. Commit `cb87071e20d5a1199e014e943c267ddd729d357a`;
fixture `f64e5b4e5b2847a704922a38fe928e528fac17344d7c158d2b55de96e2827e4c`.
Proof is existing colour-dual iff applied to the accepted lower gate.
See UPPER-PREDECESSOR-HANDOFF.md.

Upper diagonal(k,5,k) is ACCEPTED and released CLOSED. Full check
`20261003-013823-62cacb`, hashf4788b174428c98, no sorry, standard axioms;
893.4s,peak5684MiB. Commit job20261003-015354-a4d87f produced current HEAD
`c79e55d04dffaa123194174c3a282374132654c2` on
`node/SingletonUpperPascalTailGateDiagFiveOfSixLeOfInputs`. Capture
20261003-015344-5fc88b produced fixture
`b6cfeee3a45fb24a11c29974eea88a5ec6426a8c5ee7b91d4c5c5d3118357f99`.
Its four-line body applies the existing dual iff at(a,u)=(k,5); uniform
inputs cover the dual colouring. See UPPER-DIAGONAL-HANDOFF.md.

Separate lower mathematical review window-9e71ff36451f4331 and
code/library maintenance review window-62865342df4e4dcc are complete;
see LOWER-MATHEMATICAL-REVIEW.md and CODE-MAINTENANCE-REVIEW.md.
Final mathematical review window-1996886570d84676 and final code/library
review window-4ffbe9f89e244513 are complete. See FINAL-MATHEMATICAL-REVIEW.md
and FINAL-CODE-MAINTENANCE-REVIEW.md. Final inventory job20261003-015928-aac142
completed successfully. Monitor window-00dfca09a84b48ea is complete; its
observational10000-output-token target was exceeded (snapshot14048), logged
without usage reset or savings claim. Handoff and late usage reconciliation
are accounted in window-b838ed868e1b4c3e, now complete. The fixed research
deadline has passed; the host paused admission and finalization is active.
Scheduled consolidation began11:08:37Z. Fresh status is nonstale with
zero problems; canonical types confirm all four exact locks and released
claims. Git remains clean at the final SHA, fixed baseline is an ancestor,
and both R21 refs are preserved. The late inventory refresh job
20261003-071011-e127fd completed0.4s/42MiB; artifact
5a7975c61791c45dbdc3ac0663d00d2d29be8908cd0b86e1ef3e8c5a97d256e1
has unchanged proof/script inventories and only the new es run review
inline command. CONSOLIDATION-REVIEW.md records source-hash comparisons
and all-in usage, including standby. No proof jobs remain; final report
and goal completion were withheld until11:38:33.055867Z.
Finalization11:40Z: all four original-source receipts were re-inspected,
exact locks/CLOSED/no-sorry/standard axioms confirmed, and worktree clean.
There are no live proof jobs or claims and no new research/checks were
admitted. handoff-accounting-final.json and usage-late-finalization.json
preserve the completed accounting window and late recorded usage; the
final response may lag these snapshots. All approved gate obligations
are fulfilled and the compact final report is supported.
`MATHEMATICAL-HANDOFF.md` gives accepted root/helper receipts, mechanism,
failed compiler routes, exact inputs and resume instructions. Earlier
chronology is preserved in `PROGRESS-ARCHIVE-0450.md` and
`MATHEMATICAL-HANDOFF-ARCHIVE-0450.md`.
