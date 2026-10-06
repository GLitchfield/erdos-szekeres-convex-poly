# R22 final mathematical review

2026-10-03T05:59Z. Upper review window `window-1996886570d84676`.
Only configured Sol was used. This is not an independent Astra review.
The accepted lower-root mathematics was reviewed separately in
LOWER-MATHEMATICAL-REVIEW.md, window-9e71ff36451f4331.

## Accepted exact interfaces

All targets have k>=6. The diagonal targets retain the exact uniform
R20 cupblock and R21 Baek hypotheses from the reviewed brief.

| Gate | Original-source check | Type lock | Commit |
| --- | --- | --- | --- |
| Lower(5,k-1,k) | `20261002-223942-093363` | `d717e6e0c539a549` | `0281d8bbf6ec782323840a4c2643153a648124fb` |
| Lower(5,k,k), exact inputs | `20261003-002634-6a5ff2` | `87bbef437ea7141f` | `5d4fa26d8a20192c90624b23ed8a9cef90af8dd1` |
| Upper(k-1,5,k) | `20261003-010620-a45c42` | `f3116a1be4927653` | `cb87071e20d5a1199e014e943c267ddd729d357a` |
| Upper(k,5,k), exact inputs | `20261003-013823-62cacb` | `f4788b174428c98` | `c79e55d04dffaa123194174c3a282374132654c2` |

Each saved receipt and the current compiled environment say CLOSED,
lock_ok=true, sorry=false, no nonstandard axioms, and exactly
propext/Classical.choice/Quot.sound. All gate claims are released; no
proof jobs remain. These compiled facts, rather than job counts or
inventory success, establish the local theorem credit.

## Proof mechanism and interface audit

Let H=C(k-1,2)+C(k-3,2) and G=H+1. The lower singleton makes its gap
sides four-cap-free by cap extension. Decomposability exposes a genuine
root. Cup/cap coupling forces smaller lower cup parameters from upper
cap witnesses; triangular/square bounds, marker endpoints and the sharp
ordered-prefix/three-cup deficits bound the roots by H and G. Their exact
reservoirs are H+1 and G+1, giving contradictions. Every orientation,
one-sided gap and repaired k6 case is in the accepted root proof. Details,
exact helper receipts and same-k dependency order are in the lower review
and MATHEMATICAL-HANDOFF.md. No case was narrowed or delegated.

The existing singletonUpperPascalTailGate_iff_lower_dual says
Upper(a,u,k) iff Lower(u,a,k), under2<=a,2<=u,a<=k,u<=k. The upper
predecessor applies it at(a,u)=(k-1,5), and the upper diagonal at(k,5).
k>=6 supplies all four arithmetic side conditions. Both bodies are
four-line direct applications to their accepted lower counterparts.
The existing iff handles reservoir symmetry, child decomposability,
deep-split colour duality, cup/cap interchange and strong-set invariance.
No order reversal or new root case is introduced by these corollaries.

The diagonal input functions are uniform over every colouring. The iff
therefore may instantiate the lower gate at the colour-dual colouring
using exactly those same functions. The upper statement neither assumes
new dual inputs nor claims the external proofs are present on baseline.
The explicit input binders and final gate parameters were inspected in
both source and the current canonical compiled types.

## Captures and source integrity

Upper predecessor fixture
`f64e5b4e5b2847a704922a38fe928e528fac17344d7c158d2b55de96e2827e4c`
names the exact parent/module and type lockf3116a1be4927653. Its source
fingerprint `bb0c9383f2b2fa652209c0df8e0d91abbff450b51c91907023d5b357adbf5d9d`
matches the committed working module. Upper diagonal fixture
`b6cfeee3a45fb24a11c29974eea88a5ec6426a8c5ee7b91d4c5c5d3118357f99`
names its exact parent/module and lockf4788b174428c98. Its fingerprint
`50d5e50ae3ca9eb7b135927251eee00e546f38a0cf680204f2192134a3af43b2`
also matches the committed module. Both metadata records specify whole
declaration scope and standard axioms. The early final capture read/commit
ordering error was resolved by terminal-output and fingerprint inspection
before claim release. No Lean source changed after acceptance.

Final worktree is clean atc79e55d04dffaa123194174c3a282374132654c2.
Fixed baseline6e4d0e66274e9d3dd1ccdbacf9fd747deb5e1d14 is an ancestor.
R21 branches retain adf3b2f1f1e0875dc59057e7abfd46be219d88da and
05ba7924a4ba74089e6ce1f396126cddbaeefca8. No R19 worktree was accessed;
no merge, push, reset or cherry-pick occurred.

## Remaining boundary

No mathematical obligation remains for the approved gate targets. The
global happy-ending conjecture remains open. Coordinator integration and
compiled instantiation of the external inputs are still needed before
using the conditional diagonal gates unconditionally; INTEGRATION-NOTES.md
contains an explicitly uncompiled source-level sketch. The final code
inventory and review subsequently completed; see
FINAL-CODE-MAINTENANCE-REVIEW.md. Late usage reconciliation and
fixed-deadline consolidation remain. The
native goal stays active until2026-10-03T11:38:33.055867Z as instructed.
